/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridMegaExceptionalAdapter
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridMegaLinkedExactTagHandoff
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartController

/-!
# Executable mega-front / linked-deferred-tail adapter

The linked deferred controller is a tail controller: its `PUnit` recurrent
summand is only a totalization and it cannot replace the finite root/front.
This file puts the old mega front and the new tail in one finite exceptional
carrier.  Initial non-receives, old-front non-receives, tail non-receives, and
tail/tail receives are executable here.  A six-field receive record is retained
as a convenient compatibility table, but the completed adapter overwrites all
four mixed rows and all four endpoints of the two genuine shadow/owner
handoffs.  The remaining malformed or otherwise noncanonical front/front rows
have an explicit local default: emit `default` and retain the endpoint's own
old-front control.  Thus the closed kernel has no external receive-map data.

Every receive function sees only the two delivered finite controls and two
inputs.  In particular no transition can inspect a graph, orientation,
hierarchy side, leader, or strict-leader bit.  The genuine shadow/owner
handoffs install the exact marked child from `...MegaLinkedExactTagHandoff`,
rather than the obsolete marked root tag.  The mixed rows then transport that
locally carried tag into the linked tail.
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
  (controllers : ProfiledRawJointRootCompatibleInitialControllers A strategy)
  (initialBank : ProfiledRawJointInitialControllerBank A strategy)

private abbrev RetainedTag :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A strategy
    hwin

private abbrev BankControl :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl A strategy hwin

private abbrev LinkedOne :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedOneControl
    A strategy hwin

private abbrev LinkedTwo :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedTwoControl
    A strategy hwin

private abbrev TailPayload :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPayload A
    strategy hwin

private abbrev TailInnerOne :=
  FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
    (LinkedOne A strategy hwin) (TailPayload A strategy hwin) PUnit.{1}

private abbrev TailInnerTwo :=
  FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
    (LinkedTwo A strategy hwin) (TailPayload A strategy hwin) PUnit.{1}

private abbrev TailAcknowledgedOne :=
  FiniteAcknowledgedDelayedCarrier (Fin 5) (TailInnerOne A strategy hwin)

private abbrev TailAcknowledgedTwo :=
  FiniteAcknowledgedDelayedCarrier (Fin 5) (TailInnerTwo A strategy hwin)

/-- The process-one control of the complete linked deferred Mealy tail,
including both the retained controller parameter and the finite
acknowledgement relay around the pending/recurrent control.  Retaining the
parameter is essential: different strict blocks install different marked
children, so a single global fallback tag would be unsound. -/
abbrev ProfiledRawJointHybridMegaLinkedDeferredTailOneControl :=
  RetainedTag A strategy hwin × TailAcknowledgedOne A strategy hwin

/-- Process-two mirror. -/
abbrev ProfiledRawJointHybridMegaLinkedDeferredTailTwoControl :=
  RetainedTag A strategy hwin × TailAcknowledgedTwo A strategy hwin

private abbrev TailOne :=
  ProfiledRawJointHybridMegaLinkedDeferredTailOneControl A strategy hwin

private abbrev TailTwo :=
  ProfiledRawJointHybridMegaLinkedDeferredTailTwoControl A strategy hwin

noncomputable instance profiledRawJointHybridMegaLinkedDeferredTailOneFintype :
    Fintype (TailOne A strategy hwin) := by
  infer_instance

noncomputable instance profiledRawJointHybridMegaLinkedDeferredTailTwoFintype :
    Fintype (TailTwo A strategy hwin) := by
  infer_instance

private abbrev OldExceptionalOne :=
  ProfiledRawJointHybridMegaExceptionalOne A strategy hwin controllers
    initialBank

private abbrev OldExceptionalTwo :=
  ProfiledRawJointHybridMegaExceptionalTwo A strategy hwin controllers
    initialBank

private abbrev OldOne :=
  ProfiledRawJointHybridMegaOneControl A strategy hwin initialBank Unit
    (OldExceptionalOne A strategy hwin controllers initialBank)

private abbrev OldTwo :=
  ProfiledRawJointHybridMegaTwoControl A strategy hwin initialBank Unit
    (OldExceptionalTwo A strategy hwin controllers initialBank)

/-- The completed exceptional carrier is the old finite front or the linked
deferred tail.  This sum tag is a local phase tag, never a graph tag. -/
abbrev ProfiledRawJointHybridMegaLinkedExceptionalOne :=
  OldExceptionalOne A strategy hwin controllers initialBank ⊕
    TailOne A strategy hwin

/-- Process-two mirror. -/
abbrev ProfiledRawJointHybridMegaLinkedExceptionalTwo :=
  OldExceptionalTwo A strategy hwin controllers initialBank ⊕
    TailTwo A strategy hwin

private abbrev ExceptionalOne :=
  ProfiledRawJointHybridMegaLinkedExceptionalOne A strategy hwin controllers
    initialBank

private abbrev ExceptionalTwo :=
  ProfiledRawJointHybridMegaLinkedExceptionalTwo A strategy hwin controllers
    initialBank

noncomputable instance profiledRawJointHybridMegaLinkedExceptionalOneFintype :
    Fintype (ExceptionalOne A strategy hwin controllers initialBank) := by
  infer_instance

noncomputable instance profiledRawJointHybridMegaLinkedExceptionalTwoFintype :
    Fintype (ExceptionalTwo A strategy hwin controllers initialBank) := by
  infer_instance

private abbrev OneControl :=
  ProfiledRawJointHybridMegaOneControl A strategy hwin initialBank Unit
    (ExceptionalOne A strategy hwin controllers initialBank)

private abbrev TwoControl :=
  ProfiledRawJointHybridMegaTwoControl A strategy hwin initialBank Unit
    (ExceptionalTwo A strategy hwin controllers initialBank)

/-! ## Cast-free phase injections and views -/

def profiledRawJointHybridMegaLinkedLiftOldOne
    (state : OldOne A strategy hwin controllers initialBank) :
    OneControl A strategy hwin controllers initialBank :=
  match state with
  | .initial initial => .initial initial
  | .exceptional exceptional => .exceptional (.inl exceptional)
  | .rightOwner key owner => .rightOwner key owner
  | .leftReceiver key receiver => .leftReceiver key receiver

def profiledRawJointHybridMegaLinkedLiftOldTwo
    (state : OldTwo A strategy hwin controllers initialBank) :
    TwoControl A strategy hwin controllers initialBank :=
  match state with
  | .initial initial => .initial initial
  | .exceptional exceptional => .exceptional (.inl exceptional)
  | .rightReceiver key receiver => .rightReceiver key receiver
  | .leftOwner key owner => .leftOwner key owner

def profiledRawJointHybridMegaLinkedInjectTailOne
    (state : TailOne A strategy hwin) :
    OneControl A strategy hwin controllers initialBank :=
  .exceptional (.inr state)

def profiledRawJointHybridMegaLinkedInjectTailTwo
    (state : TailTwo A strategy hwin) :
    TwoControl A strategy hwin controllers initialBank :=
  .exceptional (.inr state)

inductive ProfiledRawJointHybridMegaLinkedOneView where
  | front (state : OldOne A strategy hwin controllers initialBank)
  | tail (state : TailOne A strategy hwin)

inductive ProfiledRawJointHybridMegaLinkedTwoView where
  | front (state : OldTwo A strategy hwin controllers initialBank)
  | tail (state : TailTwo A strategy hwin)

def profiledRawJointHybridMegaLinkedOneView
    (state : OneControl A strategy hwin controllers initialBank) :
    ProfiledRawJointHybridMegaLinkedOneView A strategy hwin controllers
      initialBank :=
  match state with
  | .initial initial => .front (.initial initial)
  | .exceptional (.inl exceptional) => .front (.exceptional exceptional)
  | .exceptional (.inr tail) => .tail tail
  | .rightOwner key owner => .front (.rightOwner key owner)
  | .leftReceiver key receiver => .front (.leftReceiver key receiver)

def profiledRawJointHybridMegaLinkedTwoView
    (state : TwoControl A strategy hwin controllers initialBank) :
    ProfiledRawJointHybridMegaLinkedTwoView A strategy hwin controllers
      initialBank :=
  match state with
  | .initial initial => .front (.initial initial)
  | .exceptional (.inl exceptional) => .front (.exceptional exceptional)
  | .exceptional (.inr tail) => .tail tail
  | .rightReceiver key receiver => .front (.rightReceiver key receiver)
  | .leftOwner key owner => .front (.leftOwner key owner)

/-! ## Exact linked-tail installation -/

/-- The locally ambiguous tail entry.  Its open branch is the ordinary
`.first` installation.  Its closed branch installs the same exact child at
the synchronized common-root `.both` row.  Color `1` is deliberate: a strict
receive against the old front then reforks at the canonical fresh color `0`,
while two simultaneous entries carry the same color and therefore select the
closed branch. -/
noncomputable def profiledRawJointHybridMegaLinkedTailCommonRootForkPair
    (retained : RetainedTag A strategy hwin) :
    TailAcknowledgedOne A strategy hwin ×
      TailAcknowledgedTwo A strategy hwin :=
  let openPair :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin retained
  let closedPair :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedCommonRootInitialOfState
      A strategy hwin retained.1
  let payload :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPayloadOfChild
      A strategy hwin retained.1
  let openOne : TailInnerOne A strategy hwin :=
    .inl (false, openPair.1, payload)
  let openTwo : TailInnerTwo A strategy hwin :=
    .inl (false, openPair.2, payload)
  let closedOne : TailInnerOne A strategy hwin :=
    .inl (false, closedPair.1, payload)
  let closedTwo : TailInnerTwo A strategy hwin :=
    .inl (false, closedPair.2, payload)
  (⟨.fork 1 ⟨openOne, closedOne⟩, none⟩,
    ⟨.fork 1 ⟨openTwo, closedTwo⟩, none⟩)

/-- Two controls installed by the same front round select the synchronized
common-root process-one control. -/
theorem profiledRawJointHybridMegaLinkedTailCommonRootForkPair_resolves_one
    (retained : RetainedTag A strategy hwin) :
    FiniteAcknowledgedDelayedCarrier.resolvedControl
        (profiledRawJointHybridMegaLinkedTailCommonRootForkPair A strategy hwin
          retained).1
        (profiledRawJointHybridMegaLinkedTailCommonRootForkPair A strategy hwin
          retained).2 =
      (.inl (false,
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedCommonRootInitialOfState
          A strategy hwin retained.1).1,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPayloadOfChild
          A strategy hwin retained.1) : TailInnerOne A strategy hwin) := by
  rfl

/-- Process-two synchronized resolution. -/
theorem profiledRawJointHybridMegaLinkedTailCommonRootForkPair_resolves_two
    (retained : RetainedTag A strategy hwin) :
    FiniteAcknowledgedDelayedCarrier.resolvedControl
        (profiledRawJointHybridMegaLinkedTailCommonRootForkPair A strategy hwin
          retained).2
        (profiledRawJointHybridMegaLinkedTailCommonRootForkPair A strategy hwin
          retained).1 =
      (.inl (false,
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedCommonRootInitialOfState
          A strategy hwin retained.1).2,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPayloadOfChild
          A strategy hwin retained.1) : TailInnerTwo A strategy hwin) := by
  rfl

/-- The unresolved process-one fork has one graph-blind output. -/
theorem profiledRawJointHybridMegaLinkedTailCommonRootForkPair_noRecvOne_coherent
    (retained : RetainedTag A strategy hwin) (input : In₁) :
    FiniteAcknowledgedDelayedCarrier.NoRecvOutputCoherent
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvOne
        A strategy hwin)
      (profiledRawJointHybridMegaLinkedTailCommonRootForkPair A strategy hwin
        retained).1 input := by
  rfl

/-- Process-two graph-blind coherence. -/
theorem profiledRawJointHybridMegaLinkedTailCommonRootForkPair_noRecvTwo_coherent
    (retained : RetainedTag A strategy hwin) (input : In₂) :
    FiniteAcknowledgedDelayedCarrier.NoRecvOutputCoherent
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvTwo
        A strategy hwin)
      (profiledRawJointHybridMegaLinkedTailCommonRootForkPair A strategy hwin
        retained).2 input := by
  rfl

/-- Install process one at the exact marked child denoted by a delivered
phase-live tag. -/
noncomputable def profiledRawJointHybridMegaLinkedTailInitialOne
    (tag : ProfiledRawJointHybridShadowPhaseLiveTag A strategy hwin) :
    OneControl A strategy hwin controllers initialBank :=
  let retained := tag.markedRetainedChildTag A strategy hwin
  let fork :=
    profiledRawJointHybridMegaLinkedTailCommonRootForkPair A strategy hwin
      retained
  profiledRawJointHybridMegaLinkedInjectTailOne A strategy hwin controllers
    initialBank (retained, fork.1)

/-- Process-two mirror. -/
noncomputable def profiledRawJointHybridMegaLinkedTailInitialTwo
    (tag : ProfiledRawJointHybridShadowPhaseLiveTag A strategy hwin) :
    TwoControl A strategy hwin controllers initialBank :=
  let retained := tag.markedRetainedChildTag A strategy hwin
  let fork :=
    profiledRawJointHybridMegaLinkedTailCommonRootForkPair A strategy hwin
      retained
  profiledRawJointHybridMegaLinkedInjectTailTwo A strategy hwin controllers
    initialBank (retained, fork.2)

/-! ## Arbitrary blind-prefix parent pinning

The linked tail's first receive may occur only after an arbitrarily long
one-way prefix.  The reusable live-step theorem says that this prefix cannot
change the selected parent.  Specializing it to the exact handoff tag pins
that parent to the direction-selected marked child, rather than merely to an
unspecified bank root. -/

noncomputable def
    profiledRawJointHybridMegaLinkedRightFirstReceiveParent
    (tag : ProfiledRawJointHybridShadowPhaseLiveTag A strategy hwin)
    (inputs : List In₁) : BankControl A strategy hwin :=
  let initialTag := tag.markedRetainedChildTag A strategy hwin
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin initialTag
  let delivered :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredNoRecvRunOne
      A strategy hwin
        (.inl
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialOne
            A strategy hwin initialTag) : TailInnerOne A strategy hwin)
        inputs
  let ownInitial : TailInnerTwo A strategy hwin :=
    .inl
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialTwo
        A strategy hwin initialTag)
  profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentTwo
    A strategy hwin
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
        A strategy hwin fallback.1 delivered)
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
        A strategy hwin fallback.2 ownInitial)

noncomputable def
    profiledRawJointHybridMegaLinkedLeftFirstReceiveParent
    (tag : ProfiledRawJointHybridShadowPhaseLiveTag A strategy hwin)
    (inputs : List In₂) : BankControl A strategy hwin :=
  let initialTag := tag.markedRetainedChildTag A strategy hwin
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin initialTag
  let delivered :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredNoRecvRunTwo
      A strategy hwin
        (.inl
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialTwo
            A strategy hwin initialTag) : TailInnerTwo A strategy hwin)
        inputs
  let ownInitial : TailInnerOne A strategy hwin :=
    .inl
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialOne
        A strategy hwin initialTag)
  profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOne
    A strategy hwin
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
        A strategy hwin fallback.1 ownInitial)
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
        A strategy hwin fallback.2 delivered)

@[simp] theorem
    profiledRawJointHybridMegaLinkedRightFirstReceiveParent_eq_markedBankChild
    (tag : ProfiledRawJointHybridShadowPhaseLiveTag A strategy hwin)
    (inputs : List In₁) :
    profiledRawJointHybridMegaLinkedRightFirstReceiveParent A strategy hwin tag
        inputs =
      tag.markedBankChild A strategy hwin := by
  exact
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRightFirstReceive_selectedParent
      A strategy hwin (tag.markedRetainedChildTag A strategy hwin) inputs

@[simp] theorem
    profiledRawJointHybridMegaLinkedLeftFirstReceiveParent_eq_markedBankChild
    (tag : ProfiledRawJointHybridShadowPhaseLiveTag A strategy hwin)
    (inputs : List In₂) :
    profiledRawJointHybridMegaLinkedLeftFirstReceiveParent A strategy hwin tag
        inputs =
      tag.markedBankChild A strategy hwin := by
  exact
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredLeftFirstReceive_selectedParent
      A strategy hwin (tag.markedRetainedChildTag A strategy hwin) inputs

/-! ## The finite front/front totalization seam -/

/-- Compatibility form of the total receive table.  The completed adapter
handles tail/tail receives itself and overwrites the four mixed fields below.
Only `frontFrontOne` and `frontFrontTwo` can affect a noncanonical front/front
configuration in the resulting controller. -/
structure ProfiledRawJointHybridMegaLinkedFrontReceiveMaps where
  frontFrontOne : OldOne A strategy hwin controllers initialBank → In₁ →
    OldTwo A strategy hwin controllers initialBank → In₂ →
      Out₁ × OneControl A strategy hwin controllers initialBank
  frontFrontTwo : OldTwo A strategy hwin controllers initialBank → In₂ →
    OldOne A strategy hwin controllers initialBank → In₁ →
      Out₂ × TwoControl A strategy hwin controllers initialBank
  frontTailOne : OldOne A strategy hwin controllers initialBank → In₁ →
    TailTwo A strategy hwin → In₂ →
      Out₁ × OneControl A strategy hwin controllers initialBank
  frontTailTwo : OldTwo A strategy hwin controllers initialBank → In₂ →
    TailOne A strategy hwin → In₁ →
      Out₂ × TwoControl A strategy hwin controllers initialBank
  tailFrontOne : TailOne A strategy hwin → In₁ →
    OldTwo A strategy hwin controllers initialBank → In₂ →
      Out₁ × OneControl A strategy hwin controllers initialBank
  tailFrontTwo : TailTwo A strategy hwin → In₂ →
    OldOne A strategy hwin controllers initialBank → In₁ →
      Out₂ × TwoControl A strategy hwin controllers initialBank

/-- Minimal external interface of the completed adapter.  Its two functions
totalize the front/front cases which are neither the initial root pair nor one
of the four endpoint rows of a genuine shadow/guard simultaneous entry.
Mixed configurations are not represented in this interface because their
transitions are constructed locally below. -/
structure ProfiledRawJointHybridMegaLinkedFrontFrontReceiveMaps where
  frontFrontOne : OldOne A strategy hwin controllers initialBank → In₁ →
    OldTwo A strategy hwin controllers initialBank → In₂ →
      Out₁ × OneControl A strategy hwin controllers initialBank
  frontFrontTwo : OldTwo A strategy hwin controllers initialBank → In₂ →
    OldOne A strategy hwin controllers initialBank → In₁ →
      Out₂ × TwoControl A strategy hwin controllers initialBank

/-- The actual indexed process-one control produced by a common-shadow
`noRecv`, viewed again as a state of the old mega front. -/
noncomputable def profiledRawJointHybridMegaLinkedFrontOneOfReplacementOwner
    (state : ProfiledRawJointHybridOneReplacementOwner A strategy hwin) :
    OldOne A strategy hwin controllers initialBank :=
  let recurrent :=
    profiledRawJointHybridOneReplacementOwnerToMega A strategy hwin
      initialBank state
  .rightOwner recurrent.1 recurrent.2

/-- Process-two left-live replacement mirror. -/
noncomputable def profiledRawJointHybridMegaLinkedFrontTwoOfReplacementOwner
    (state : ProfiledRawJointHybridTwoReplacementOwner A strategy hwin) :
    OldTwo A strategy hwin controllers initialBank :=
  let recurrent :=
    profiledRawJointHybridTwoReplacementOwnerToMega A strategy hwin
      initialBank state
  .leftOwner recurrent.1 recurrent.2

/-! ### Finite initial sibling-front receive steps -/

/-- Close a delivered installed right receiver and execute the first receive
at its checked recurrent left root. -/
noncomputable def
    profiledRawJointHybridMegaLinkedInitialRightReceiverCloseOne
    (receiver : ProfiledRawJointHybridInitialRightInstalledReceiver A strategy
      hwin)
    (inputOne : In₁) (inputTwo : In₂) :
    Out₁ × OldOne A strategy hwin controllers initialBank := by
  classical
  cases htarget : receiver.2.2.2 with
  | none => exact (default, .initial ())
  | some target =>
      cases hroot :
          profiledRawJointHybridMegaInitialRightTargetRoot? A strategy hwin
            initialBank receiver.1 target with
      | none => exact (default, .initial ())
      | some targetRoot =>
          let child :=
            profiledRawJointHybridMegaChildOfInitialSiblingTarget A strategy
              hwin initialBank targetRoot.1
          exact profiledRawJointHybridMegaStartLeftReceiver A strategy hwin
            controllers initialBank child targetRoot.2 receiver.2.1 inputOne
              inputTwo

/-- Close a delivered installed left receiver into the recurrent right
receiver family. -/
noncomputable def
    profiledRawJointHybridMegaLinkedInitialLeftReceiverCloseTwo
    (receiver : ProfiledRawJointHybridInitialLeftInstalledReceiver A strategy
      hwin)
    (inputTwo : In₂) (inputOne : In₁) :
    Out₂ × OldTwo A strategy hwin controllers initialBank := by
  classical
  cases htarget : receiver.2.2.2 with
  | none => exact (default, .initial ())
  | some target =>
      cases hroot :
          profiledRawJointHybridMegaInitialLeftTargetRoot? A strategy hwin
            initialBank receiver.1 target with
      | none => exact (default, .initial ())
      | some targetRoot =>
          let child :=
            profiledRawJointHybridMegaChildOfInitialSiblingTarget A strategy
              hwin initialBank targetRoot.1
          exact profiledRawJointHybridMegaStartRightReceiver A strategy hwin
            controllers initialBank child targetRoot.2 receiver.2.1 inputTwo
              inputOne

/-- Continue an installed right receiver with a genuinely delivered owner of
the same installation.  The mismatch branch merely totalizes malformed
finite controls. -/
noncomputable def
    profiledRawJointHybridMegaLinkedInitialRightReceiverRecvTwo
    (receiver : ProfiledRawJointHybridInitialRightInstalledReceiver A strategy
      hwin)
    (owner : ProfiledRawJointHybridInitialRightInstalledOwner A strategy hwin)
    (inputTwo : In₂) (inputOne : In₁) :
    Out₂ × OldTwo A strategy hwin controllers initialBank := by
  classical
  rcases receiver with ⟨receiverInstallation, receiverState⟩
  rcases owner with ⟨ownerInstallation, ownerState⟩
  by_cases hinstallation : ownerInstallation = receiverInstallation
  · subst ownerInstallation
    let next := stepProfiledRawJointHybridInitialRightReceiverAt A strategy
      hwin receiverInstallation ownerState receiverState (inputTwo, inputOne)
    exact (next.1, .exceptional
      (profiledRawJointHybridMegaExceptionalTwoOfPinnedInitial A strategy hwin
        controllers initialBank
          (.inr (.inr (.inl ⟨receiverInstallation, next.2⟩)))))
  · exact (default, .initial ())

/-- Installed left-receiver continuation mirror. -/
noncomputable def
    profiledRawJointHybridMegaLinkedInitialLeftReceiverRecvOne
    (receiver : ProfiledRawJointHybridInitialLeftInstalledReceiver A strategy
      hwin)
    (owner : ProfiledRawJointHybridInitialLeftInstalledOwner A strategy hwin)
    (inputOne : In₁) (inputTwo : In₂) :
    Out₁ × OldOne A strategy hwin controllers initialBank := by
  classical
  rcases receiver with ⟨receiverInstallation, receiverState⟩
  rcases owner with ⟨ownerInstallation, ownerState⟩
  by_cases hinstallation : ownerInstallation = receiverInstallation
  · subst ownerInstallation
    let next := stepProfiledRawJointHybridInitialLeftReceiverAt A strategy hwin
      receiverInstallation ownerState receiverState (inputOne, inputTwo)
    exact (next.1, .exceptional
      (profiledRawJointHybridMegaExceptionalOneOfPinnedInitial A strategy hwin
        controllers initialBank
          (.inr (.inr (.inr ⟨receiverInstallation, next.2⟩)))))
  · exact (default, .initial ())

/-- Start the ordinary recurrent right receiver from a delivered ordinary
left receiver, ignoring a now-obsolete finite-front state. -/
noncomputable def
    profiledRawJointHybridMegaLinkedStartRightReceiverFromLeftReceiverTwo
    (key : ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank)
    (receiver : ProfiledRawJointHybridMegaLeftReceiver A strategy hwin
      initialBank key)
    (inputTwo : In₂) (inputOne : In₁) :
    Out₂ × OldTwo A strategy hwin controllers initialBank :=
  let source := profiledRawJointHybridMegaChildSource A strategy hwin
    initialBank key
  let policy := profiledRawJointHybridMegaChildPolicy A strategy hwin
    initialBank key
  let bank := profiledRawJointHybridMegaChildControllerBank A strategy hwin
    initialBank key
  let next := profiledRawJointUnitPolicyStartRightReceiver A strategy source
    policy bank receiver (inputTwo, inputOne)
  (next.1, .rightReceiver key next.2)

/-- Process-one mirror, starting an ordinary left receiver from a delivered
ordinary right receiver. -/
noncomputable def
    profiledRawJointHybridMegaLinkedStartLeftReceiverFromRightReceiverOne
    (key : ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank)
    (receiver : ProfiledRawJointHybridMegaRightReceiver A strategy hwin
      initialBank key)
    (inputOne : In₁) (inputTwo : In₂) :
    Out₁ × OldOne A strategy hwin controllers initialBank :=
  let source := profiledRawJointHybridMegaChildSource A strategy hwin
    initialBank key
  let policy := profiledRawJointHybridMegaChildPolicy A strategy hwin
    initialBank key
  let bank := profiledRawJointHybridMegaChildControllerBank A strategy hwin
    initialBank key
  let next := profiledRawJointUnitPolicyStartLeftReceiver A strategy source
    policy bank receiver (inputOne, inputTwo)
  (next.1, .leftReceiver key next.2)

/-- Continue an ordinary left receiver using the checked left owner rebuilt
from a synchronized finite right receiver target. -/
noncomputable def
    profiledRawJointHybridMegaLinkedContinueLeftReceiverFromInitialRightTargetOne
    (key : ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank)
    (receiver : ProfiledRawJointHybridMegaLeftReceiver A strategy hwin
      initialBank key)
    (front : ProfiledRawJointHybridInitialRightInstalledReceiver A strategy
      hwin)
    (inputOne : In₁) (inputTwo : In₂) :
    Out₁ × OldOne A strategy hwin controllers initialBank := by
  classical
  cases htarget : front.2.2.2 with
  | none => exact (default, .leftReceiver key receiver)
  | some target =>
      cases hroot :
          profiledRawJointHybridMegaInitialRightTargetRoot? A strategy hwin
            initialBank front.1 target with
      | none => exact (default, .leftReceiver key receiver)
      | some targetRoot =>
          let child :=
            profiledRawJointHybridMegaChildOfInitialSiblingTarget A strategy
              hwin initialBank targetRoot.1
          by_cases hkey : child = key
          · subst key
            let source := profiledRawJointHybridMegaChildSource A strategy hwin
              initialBank child
            let policy := profiledRawJointHybridMegaChildPolicy A strategy hwin
              initialBank child
            let bank := profiledRawJointHybridMegaChildControllerBank A
              strategy hwin initialBank child
            let owner := initialProfiledRawJointUnitLeftPolicyOwner A strategy
              source policy bank targetRoot.2
            let next := continueProfiledRawJointUnitLeftPolicyReceiver A
              strategy source policy bank receiver owner (inputOne, inputTwo)
            exact (next.1, .leftReceiver child next.2)
          · exact (default, .leftReceiver key receiver)

/-- Continue an ordinary right receiver from the checked right owner rebuilt
from a synchronized finite left receiver target. -/
noncomputable def
    profiledRawJointHybridMegaLinkedContinueRightReceiverFromInitialLeftTargetTwo
    (key : ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank)
    (receiver : ProfiledRawJointHybridMegaRightReceiver A strategy hwin
      initialBank key)
    (front : ProfiledRawJointHybridInitialLeftInstalledReceiver A strategy
      hwin)
    (inputTwo : In₂) (inputOne : In₁) :
    Out₂ × OldTwo A strategy hwin controllers initialBank := by
  classical
  cases htarget : front.2.2.2 with
  | none => exact (default, .rightReceiver key receiver)
  | some target =>
      cases hroot :
          profiledRawJointHybridMegaInitialLeftTargetRoot? A strategy hwin
            initialBank front.1 target with
      | none => exact (default, .rightReceiver key receiver)
      | some targetRoot =>
          let child :=
            profiledRawJointHybridMegaChildOfInitialSiblingTarget A strategy
              hwin initialBank targetRoot.1
          by_cases hkey : child = key
          · subst key
            let source := profiledRawJointHybridMegaChildSource A strategy hwin
              initialBank child
            let policy := profiledRawJointHybridMegaChildPolicy A strategy hwin
              initialBank child
            let bank := profiledRawJointHybridMegaChildControllerBank A
              strategy hwin initialBank child
            let owner := initialProfiledRawJointUnitRightPolicyOwner A strategy
              source policy bank targetRoot.2
            let next := continueProfiledRawJointUnitRightPolicyReceiver A
              strategy source policy bank receiver owner (inputTwo, inputOne)
            exact (next.1, .rightReceiver child next.2)
          · exact (default, .rightReceiver key receiver)

/-- Canonical partial closure of the old front/front table.

The common/common and shadow/shadow rows are reachable: a simultaneous round
creates a pair of shadows, and every further simultaneous round refreshes that
pair.  They therefore have to execute the honest common-front table here.  The
remaining fallback still totalizes malformed or not-yet-wired startup rows by
retaining the endpoint's own local control. -/
noncomputable def profiledRawJointHybridMegaLinkedDefaultFrontFrontReceiveMaps :
    ProfiledRawJointHybridMegaLinkedFrontFrontReceiveMaps A strategy hwin
      controllers initialBank where
  frontFrontOne := fun one inputOne two inputTwo =>
    match one, two with
    | .exceptional (.inr (.inl initialShadowOne)),
        .exceptional (.inr (.inl initialShadowTwo)) =>
        let next := profiledRawJointHybridMegaInitialToCoupledOne A strategy
          hwin controllers initialShadowTwo inputOne inputTwo
        (next.1,
          profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin
            controllers initialBank
              (.exceptional
                (profiledRawJointHybridMegaExceptionalOneOfPinnedInitial A
                  strategy hwin controllers initialBank
                    (.inr (.inl next.2)))))
    | .exceptional (.inr (.inr (.inr (.inr (.inl _coupledOne))))),
        .exceptional (.inr (.inr (.inr (.inr (.inl coupledTwo))))) =>
        let next :=
          profiledRawJointHybridMegaCoupledStartLeftReceiverOne A strategy hwin
            coupledTwo inputOne inputTwo
        (next.1,
          profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin
            controllers initialBank
              (.exceptional
                (profiledRawJointHybridMegaExceptionalOneOfPinnedInitial A
                  strategy hwin controllers initialBank
                    (.inr (.inr (.inr next.2))))))
    | .exceptional
          (.inr (.inr (.inr (.inr (.inr (.inl _rightOwner)))))),
        .exceptional
          (.inr (.inr (.inr (.inr (.inr (.inl rightReceiver)))))) =>
        let next :=
          profiledRawJointHybridMegaLinkedInitialRightReceiverCloseOne A
            strategy hwin controllers initialBank rightReceiver inputOne
              inputTwo
        (next.1,
          profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin
            controllers initialBank next.2)
    | .exceptional
          (.inr (.inr (.inr (.inr (.inr (.inr leftReceiver)))))),
        .exceptional
          (.inr (.inr (.inr (.inr (.inr (.inr leftOwner)))))) =>
        let next :=
          profiledRawJointHybridMegaLinkedInitialLeftReceiverRecvOne A strategy
            hwin controllers initialBank leftReceiver leftOwner inputOne
              inputTwo
        (next.1,
          profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin
            controllers initialBank next.2)
    | .exceptional
          (.inr (.inr (.inr (.inr (.inr (.inr _leftReceiver)))))),
        .exceptional
          (.inr (.inr (.inr (.inr (.inr (.inl rightReceiver)))))) =>
        let next :=
          profiledRawJointHybridMegaLinkedInitialRightReceiverCloseOne A
            strategy hwin controllers initialBank rightReceiver inputOne
              inputTwo
        (next.1,
          profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin
            controllers initialBank next.2)
    | .leftReceiver key receiver,
        .exceptional
          (.inr (.inr (.inr (.inr (.inr (.inl rightReceiver)))))) =>
        let next :=
          profiledRawJointHybridMegaLinkedContinueLeftReceiverFromInitialRightTargetOne
            A strategy hwin controllers initialBank key receiver rightReceiver
              inputOne inputTwo
        (next.1,
          profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin
            controllers initialBank next.2)
    | .exceptional
          (.inr (.inr (.inr (.inr (.inr (.inr _leftReceiver)))))),
        .rightReceiver key receiver =>
        let next :=
          profiledRawJointHybridMegaLinkedStartLeftReceiverFromRightReceiverOne
            A strategy hwin controllers initialBank key receiver inputOne
              inputTwo
        (next.1,
          profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin
            controllers initialBank next.2)
    | .exceptional (.inr (.inr (.inl (.inl commonOne)))),
        .exceptional (.inr (.inr (.inl (.inl _commonTwo)))) =>
        let next := profiledRawJointHybridCommonToOneShadow A strategy hwin
          commonOne inputOne inputTwo
        (next.1,
          profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin
            controllers initialBank
              (.exceptional
                (profiledRawJointHybridMegaExceptionalOneOfCommon A strategy
                  hwin controllers initialBank (.inr (.inl next.2)))))
    | .exceptional (.inr (.inr (.inl (.inr (.inl shadowOne))))),
        .exceptional (.inr (.inr (.inl (.inr (.inl shadowTwo))))) =>
        let next := profiledRawJointHybridOneShadowRecvCommon A strategy hwin
          shadowOne shadowTwo inputOne inputTwo
        (next.1,
          profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin
            controllers initialBank
              (.exceptional
                (profiledRawJointHybridMegaExceptionalOneOfCommon A strategy
                  hwin controllers initialBank (.inr (.inl next.2)))))
    | .rightOwner (.inr (.inl _replacement)) _owner,
        .exceptional (.inr (.inr (.inl (.inr (.inl shadowTwo))))) =>
        let tag := profiledRawJointHybridShadowPhaseLiveRightTag A strategy hwin
          shadowTwo.origin shadowTwo.input
        (default,
          profiledRawJointHybridMegaLinkedTailInitialOne A strategy hwin
            controllers initialBank tag)
    | .exceptional (.inr (.inr (.inl (.inr (.inl shadowOne))))),
        .leftOwner (.inr (.inl _replacement)) _owner =>
        let tag := profiledRawJointHybridShadowPhaseLiveLeftTag A strategy hwin
          shadowOne.origin shadowOne.input
        (default,
          profiledRawJointHybridMegaLinkedTailInitialOne A strategy hwin
            controllers initialBank tag)
    | _, _ =>
        (default,
          profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin
            controllers initialBank one)
  frontFrontTwo := fun two inputTwo one inputOne =>
    match two, one with
    | .exceptional (.inr (.inl initialShadowTwo)),
        .exceptional (.inr (.inl initialShadowOne)) =>
        let next := profiledRawJointHybridMegaInitialToCoupledTwo A strategy
          hwin controllers initialShadowOne inputTwo inputOne
        (next.1,
          profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin
            controllers initialBank
              (.exceptional
                (profiledRawJointHybridMegaExceptionalTwoOfPinnedInitial A
                  strategy hwin controllers initialBank
                    (.inr (.inl next.2)))))
    | .exceptional (.inr (.inr (.inr (.inr (.inl _coupledTwo))))),
        .exceptional (.inr (.inr (.inr (.inr (.inl coupledOne))))) =>
        let next :=
          profiledRawJointHybridMegaCoupledStartRightReceiverTwo A strategy
            hwin coupledOne inputTwo inputOne
        (next.1,
          profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin
            controllers initialBank
              (.exceptional
                (profiledRawJointHybridMegaExceptionalTwoOfPinnedInitial A
                  strategy hwin controllers initialBank
                    (.inr (.inr (.inl next.2))))))
    | .exceptional
          (.inr (.inr (.inr (.inr (.inr (.inl rightReceiver)))))),
        .exceptional
          (.inr (.inr (.inr (.inr (.inr (.inl rightOwner)))))) =>
        let next :=
          profiledRawJointHybridMegaLinkedInitialRightReceiverRecvTwo A strategy
            hwin controllers initialBank rightReceiver rightOwner inputTwo
              inputOne
        (next.1,
          profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin
            controllers initialBank next.2)
    | .exceptional
          (.inr (.inr (.inr (.inr (.inr (.inr _leftOwner)))))),
        .exceptional
          (.inr (.inr (.inr (.inr (.inr (.inr leftReceiver)))))) =>
        let next :=
          profiledRawJointHybridMegaLinkedInitialLeftReceiverCloseTwo A strategy
            hwin controllers initialBank leftReceiver inputTwo inputOne
        (next.1,
          profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin
            controllers initialBank next.2)
    | .exceptional
          (.inr (.inr (.inr (.inr (.inr (.inl _rightReceiver)))))),
        .exceptional
          (.inr (.inr (.inr (.inr (.inr (.inr leftReceiver)))))) =>
        let next :=
          profiledRawJointHybridMegaLinkedInitialLeftReceiverCloseTwo A strategy
            hwin controllers initialBank leftReceiver inputTwo inputOne
        (next.1,
          profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin
            controllers initialBank next.2)
    | .exceptional
          (.inr (.inr (.inr (.inr (.inr (.inl _rightReceiver)))))),
        .leftReceiver key receiver =>
        let next :=
          profiledRawJointHybridMegaLinkedStartRightReceiverFromLeftReceiverTwo
            A strategy hwin controllers initialBank key receiver inputTwo
              inputOne
        (next.1,
          profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin
            controllers initialBank next.2)
    | .rightReceiver key receiver,
        .exceptional
          (.inr (.inr (.inr (.inr (.inr (.inr leftReceiver)))))) =>
        let next :=
          profiledRawJointHybridMegaLinkedContinueRightReceiverFromInitialLeftTargetTwo
            A strategy hwin controllers initialBank key receiver leftReceiver
              inputTwo inputOne
        (next.1,
          profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin
            controllers initialBank next.2)
    | .exceptional (.inr (.inr (.inl (.inl commonTwo)))),
        .exceptional (.inr (.inr (.inl (.inl _commonOne)))) =>
        let next := profiledRawJointHybridCommonToTwoShadow A strategy hwin
          commonTwo inputTwo inputOne
        (next.1,
          profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin
            controllers initialBank
              (.exceptional
                (profiledRawJointHybridMegaExceptionalTwoOfCommon A strategy
                  hwin controllers initialBank (.inr (.inl next.2)))))
    | .exceptional (.inr (.inr (.inl (.inr (.inl shadowTwo))))),
        .exceptional (.inr (.inr (.inl (.inr (.inl shadowOne))))) =>
        let next := profiledRawJointHybridTwoShadowRecvCommon A strategy hwin
          shadowTwo shadowOne inputTwo inputOne
        (next.1,
          profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin
            controllers initialBank
              (.exceptional
                (profiledRawJointHybridMegaExceptionalTwoOfCommon A strategy
                  hwin controllers initialBank (.inr (.inl next.2)))))
    | .exceptional (.inr (.inr (.inl (.inr (.inl shadowTwo))))),
        .rightOwner (.inr (.inl _replacement)) _owner =>
        let tag := profiledRawJointHybridShadowPhaseLiveRightTag A strategy hwin
          shadowTwo.origin shadowTwo.input
        (default,
          profiledRawJointHybridMegaLinkedTailInitialTwo A strategy hwin
            controllers initialBank tag)
    | .leftOwner (.inr (.inl _replacement)) _owner,
        .exceptional (.inr (.inr (.inl (.inr (.inl shadowOne))))) =>
        let tag := profiledRawJointHybridShadowPhaseLiveLeftTag A strategy hwin
          shadowOne.origin shadowOne.input
        (default,
          profiledRawJointHybridMegaLinkedTailInitialTwo A strategy hwin
            controllers initialBank tag)
    | _, _ =>
        (default,
          profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin
            controllers initialBank two)

@[simp] theorem
    profiledRawJointHybridMegaLinkedDefaultFrontFrontReceiveMaps_initialShadows_one
    (shadowOne : ProfiledRawJointHybridInitialOneShadow A strategy hwin
      controllers)
    (shadowTwo : ProfiledRawJointHybridInitialTwoShadow A strategy hwin
      controllers)
    (inputOne : In₁) (inputTwo : In₂) :
    (profiledRawJointHybridMegaLinkedDefaultFrontFrontReceiveMaps A strategy
      hwin controllers initialBank).frontFrontOne
        (.exceptional
          (profiledRawJointHybridMegaExceptionalOneOfInitialShadow A strategy
            hwin controllers initialBank shadowOne)) inputOne
        (.exceptional
          (profiledRawJointHybridMegaExceptionalTwoOfInitialShadow A strategy
            hwin controllers initialBank shadowTwo)) inputTwo =
      let next := profiledRawJointHybridMegaInitialToCoupledOne A strategy hwin
        controllers shadowTwo inputOne inputTwo
      (next.1,
        profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin controllers
          initialBank
            (.exceptional
              (profiledRawJointHybridMegaExceptionalOneOfPinnedInitial A
                strategy hwin controllers initialBank
                  (.inr (.inl next.2))))) :=
  rfl

@[simp] theorem
    profiledRawJointHybridMegaLinkedDefaultFrontFrontReceiveMaps_initialShadows_two
    (shadowTwo : ProfiledRawJointHybridInitialTwoShadow A strategy hwin
      controllers)
    (shadowOne : ProfiledRawJointHybridInitialOneShadow A strategy hwin
      controllers)
    (inputTwo : In₂) (inputOne : In₁) :
    (profiledRawJointHybridMegaLinkedDefaultFrontFrontReceiveMaps A strategy
      hwin controllers initialBank).frontFrontTwo
        (.exceptional
          (profiledRawJointHybridMegaExceptionalTwoOfInitialShadow A strategy
            hwin controllers initialBank shadowTwo)) inputTwo
        (.exceptional
          (profiledRawJointHybridMegaExceptionalOneOfInitialShadow A strategy
            hwin controllers initialBank shadowOne)) inputOne =
      let next := profiledRawJointHybridMegaInitialToCoupledTwo A strategy hwin
        controllers shadowOne inputTwo inputOne
      (next.1,
        profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin controllers
          initialBank
            (.exceptional
              (profiledRawJointHybridMegaExceptionalTwoOfPinnedInitial A
                strategy hwin controllers initialBank
                  (.inr (.inl next.2))))) :=
  rfl

@[simp] theorem
    profiledRawJointHybridMegaLinkedDefaultFrontFrontReceiveMaps_coupled_one
    (coupledOne : ProfiledRawJointHybridMegaCoupledInitialOne A strategy hwin)
    (coupledTwo : ProfiledRawJointHybridMegaCoupledInitialTwo A strategy hwin)
    (inputOne : In₁) (inputTwo : In₂) :
    (profiledRawJointHybridMegaLinkedDefaultFrontFrontReceiveMaps A strategy
      hwin controllers initialBank).frontFrontOne
        (.exceptional
          (profiledRawJointHybridMegaExceptionalOneOfPinnedInitial A strategy
            hwin controllers initialBank (.inr (.inl coupledOne)))) inputOne
        (.exceptional
          (profiledRawJointHybridMegaExceptionalTwoOfPinnedInitial A strategy
            hwin controllers initialBank (.inr (.inl coupledTwo)))) inputTwo =
      let next :=
        profiledRawJointHybridMegaCoupledStartLeftReceiverOne A strategy hwin
          coupledTwo inputOne inputTwo
      (next.1,
        profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin controllers
          initialBank (.exceptional
            (profiledRawJointHybridMegaExceptionalOneOfPinnedInitial A strategy
              hwin controllers initialBank
                (.inr (.inr (.inr next.2)))))) :=
  rfl

@[simp] theorem
    profiledRawJointHybridMegaLinkedDefaultFrontFrontReceiveMaps_coupled_two
    (coupledTwo : ProfiledRawJointHybridMegaCoupledInitialTwo A strategy hwin)
    (coupledOne : ProfiledRawJointHybridMegaCoupledInitialOne A strategy hwin)
    (inputTwo : In₂) (inputOne : In₁) :
    (profiledRawJointHybridMegaLinkedDefaultFrontFrontReceiveMaps A strategy
      hwin controllers initialBank).frontFrontTwo
        (.exceptional
          (profiledRawJointHybridMegaExceptionalTwoOfPinnedInitial A strategy
            hwin controllers initialBank (.inr (.inl coupledTwo)))) inputTwo
        (.exceptional
          (profiledRawJointHybridMegaExceptionalOneOfPinnedInitial A strategy
            hwin controllers initialBank (.inr (.inl coupledOne)))) inputOne =
      let next :=
        profiledRawJointHybridMegaCoupledStartRightReceiverTwo A strategy hwin
          coupledOne inputTwo inputOne
      (next.1,
        profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin controllers
          initialBank (.exceptional
            (profiledRawJointHybridMegaExceptionalTwoOfPinnedInitial A strategy
              hwin controllers initialBank
                (.inr (.inr (.inl next.2)))))) :=
  rfl

@[simp] theorem
    profiledRawJointHybridMegaLinkedDefaultFrontFrontReceiveMaps_common_one
    (commonOne commonTwo :
      ProfiledRawJointHybridCommonControl A strategy hwin)
    (inputOne : In₁) (inputTwo : In₂) :
    (profiledRawJointHybridMegaLinkedDefaultFrontFrontReceiveMaps A strategy
      hwin controllers initialBank).frontFrontOne
        (.exceptional
          (profiledRawJointHybridMegaExceptionalOneOfCommon A strategy hwin
            controllers initialBank (.inl commonOne))) inputOne
        (.exceptional
          (profiledRawJointHybridMegaExceptionalTwoOfCommon A strategy hwin
            controllers initialBank (.inl commonTwo))) inputTwo =
      let next := profiledRawJointHybridCommonToOneShadow A strategy hwin
        commonOne inputOne inputTwo
      (next.1,
        profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin controllers
          initialBank
            (.exceptional
              (profiledRawJointHybridMegaExceptionalOneOfCommon A strategy hwin
                controllers initialBank (.inr (.inl next.2))))) :=
  rfl

@[simp] theorem
    profiledRawJointHybridMegaLinkedDefaultFrontFrontReceiveMaps_common_two
    (commonTwo commonOne :
      ProfiledRawJointHybridCommonControl A strategy hwin)
    (inputTwo : In₂) (inputOne : In₁) :
    (profiledRawJointHybridMegaLinkedDefaultFrontFrontReceiveMaps A strategy
      hwin controllers initialBank).frontFrontTwo
        (.exceptional
          (profiledRawJointHybridMegaExceptionalTwoOfCommon A strategy hwin
            controllers initialBank (.inl commonTwo))) inputTwo
        (.exceptional
          (profiledRawJointHybridMegaExceptionalOneOfCommon A strategy hwin
            controllers initialBank (.inl commonOne))) inputOne =
      let next := profiledRawJointHybridCommonToTwoShadow A strategy hwin
        commonTwo inputTwo inputOne
      (next.1,
        profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin controllers
          initialBank
            (.exceptional
              (profiledRawJointHybridMegaExceptionalTwoOfCommon A strategy hwin
                controllers initialBank (.inr (.inl next.2))))) :=
  rfl

@[simp] theorem
    profiledRawJointHybridMegaLinkedDefaultFrontFrontReceiveMaps_shadows_one
    (shadowOne : ProfiledRawJointHybridOneShadow A strategy hwin)
    (shadowTwo : ProfiledRawJointHybridTwoShadow A strategy hwin)
    (inputOne : In₁) (inputTwo : In₂) :
    (profiledRawJointHybridMegaLinkedDefaultFrontFrontReceiveMaps A strategy
      hwin controllers initialBank).frontFrontOne
        (.exceptional
          (.inr (.inr (.inl (.inr (.inl shadowOne)))))) inputOne
        (.exceptional
          (.inr (.inr (.inl (.inr (.inl shadowTwo)))))) inputTwo =
      let next := profiledRawJointHybridOneShadowRecvCommon A strategy hwin
        shadowOne shadowTwo inputOne inputTwo
      (next.1,
        profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin controllers
          initialBank
            (.exceptional
              (.inr (.inr (.inl (.inr (.inl next.2))))))) :=
  rfl

@[simp] theorem
    profiledRawJointHybridMegaLinkedDefaultFrontFrontReceiveMaps_shadows_two
    (shadowTwo : ProfiledRawJointHybridTwoShadow A strategy hwin)
    (shadowOne : ProfiledRawJointHybridOneShadow A strategy hwin)
    (inputTwo : In₂) (inputOne : In₁) :
    (profiledRawJointHybridMegaLinkedDefaultFrontFrontReceiveMaps A strategy
      hwin controllers initialBank).frontFrontTwo
        (.exceptional
          (.inr (.inr (.inl (.inr (.inl shadowTwo)))))) inputTwo
        (.exceptional
          (.inr (.inr (.inl (.inr (.inl shadowOne)))))) inputOne =
      let next := profiledRawJointHybridTwoShadowRecvCommon A strategy hwin
        shadowTwo shadowOne inputTwo inputOne
      (next.1,
        profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin controllers
          initialBank
            (.exceptional
              (.inr (.inr (.inl (.inr (.inl next.2))))))) :=
  rfl

/-! ## Exact genuine front handoffs

The six functions above are a total table, so they must also assign values to
malformed pairs of front controls.  The two simultaneous pairs which actually
finish the common shadow are not residual choices.  At each pair, the shadow
receiver computes the phase-live tag and the complementary owner endpoint
computes the same tag from the delivered shadow.  Thus all four local rows
install the linked tail at the exact same marked child.  We enforce those four
rows by an override.  Notice that each test is solely a pattern match on
delivered finite controls.

The four mixed rows are also canonical below: one endpoint has installed this
tag while the still-blind endpoint is finishing its old guard-owner prefix.
Consequently the completed adapter depends on the supplied table only at the
two noncanonical front/front rows. -/

private abbrev OneShadow :=
  ProfiledRawJointHybridOneShadow A strategy hwin

private abbrev TwoShadow :=
  ProfiledRawJointHybridTwoShadow A strategy hwin

private abbrev RightGuardOwner :=
  ProfiledRawJointHybridRightGuardOwner A strategy hwin

private abbrev LeftGuardOwner :=
  ProfiledRawJointHybridLeftGuardOwner A strategy hwin

/-- Named embedding of a process-one common control in the old mega front. -/
def profiledRawJointHybridMegaLinkedFrontOneOfCommon
    (common : ProfiledRawJointHybridCommonControl A strategy hwin) :
    OldOne A strategy hwin controllers initialBank :=
  .exceptional (.inr (.inr (.inl (.inl common))))

/-- Process-two common-control mirror. -/
def profiledRawJointHybridMegaLinkedFrontTwoOfCommon
    (common : ProfiledRawJointHybridCommonControl A strategy hwin) :
    OldTwo A strategy hwin controllers initialBank :=
  .exceptional (.inr (.inr (.inl (.inl common))))

/-- Named embedding of a process-one common shadow in the old mega front. -/
def profiledRawJointHybridMegaLinkedFrontOneOfShadow
    (shadow : OneShadow A strategy hwin) :
    OldOne A strategy hwin controllers initialBank :=
  .exceptional (.inr (.inr (.inl (.inr (.inl shadow)))))

/-- Process-two shadow embedding. -/
def profiledRawJointHybridMegaLinkedFrontTwoOfShadow
    (shadow : TwoShadow A strategy hwin) :
    OldTwo A strategy hwin controllers initialBank :=
  .exceptional (.inr (.inr (.inl (.inr (.inl shadow)))))

/-- Named process-one strict-right guard-owner embedding. -/
def profiledRawJointHybridMegaLinkedFrontOneOfRightGuardOwner
    (owner : RightGuardOwner A strategy hwin) :
    OldOne A strategy hwin controllers initialBank :=
  .exceptional (.inr (.inr (.inl (.inr (.inr (.inl owner))))))

/-- Named process-two strict-left guard-owner embedding. -/
def profiledRawJointHybridMegaLinkedFrontTwoOfLeftGuardOwner
    (owner : LeftGuardOwner A strategy hwin) :
    OldTwo A strategy hwin controllers initialBank :=
  .exceptional (.inr (.inr (.inl (.inr (.inr (.inl owner))))))

/- A replacement owner and the informed shadow are a reachable resolving
pair.  The shadow supplies the actual strict-side tag; the replacement owner
itself was created one blind round earlier and deliberately does not guess
that tag.  The handoff output is immaterial to parity acceptance because the
installed linked tail starts after this finite boundary round. -/
@[simp] theorem
    profiledRawJointHybridMegaLinkedDefaultFrontFrontReceiveMaps_rightReplacement_one
    (owner : ProfiledRawJointHybridOneReplacementOwner A strategy hwin)
    (shadow : TwoShadow A strategy hwin)
    (inputOne : In₁) (inputTwo : In₂) :
    (profiledRawJointHybridMegaLinkedDefaultFrontFrontReceiveMaps A strategy
      hwin controllers initialBank).frontFrontOne
        (profiledRawJointHybridMegaLinkedFrontOneOfReplacementOwner A strategy
          hwin controllers initialBank owner) inputOne
        (profiledRawJointHybridMegaLinkedFrontTwoOfShadow A strategy hwin
          controllers initialBank shadow) inputTwo =
      (default,
        profiledRawJointHybridMegaLinkedTailInitialOne A strategy hwin
          controllers initialBank
            (profiledRawJointHybridShadowPhaseLiveRightTag A strategy hwin
              shadow.origin shadow.input)) :=
  rfl

@[simp] theorem
    profiledRawJointHybridMegaLinkedDefaultFrontFrontReceiveMaps_rightReplacement_two
    (shadow : TwoShadow A strategy hwin)
    (owner : ProfiledRawJointHybridOneReplacementOwner A strategy hwin)
    (inputTwo : In₂) (inputOne : In₁) :
    (profiledRawJointHybridMegaLinkedDefaultFrontFrontReceiveMaps A strategy
      hwin controllers initialBank).frontFrontTwo
        (profiledRawJointHybridMegaLinkedFrontTwoOfShadow A strategy hwin
          controllers initialBank shadow) inputTwo
        (profiledRawJointHybridMegaLinkedFrontOneOfReplacementOwner A strategy
          hwin controllers initialBank owner) inputOne =
      (default,
        profiledRawJointHybridMegaLinkedTailInitialTwo A strategy hwin
          controllers initialBank
            (profiledRawJointHybridShadowPhaseLiveRightTag A strategy hwin
              shadow.origin shadow.input)) :=
  rfl

@[simp] theorem
    profiledRawJointHybridMegaLinkedDefaultFrontFrontReceiveMaps_leftReplacement_one
    (shadow : OneShadow A strategy hwin)
    (owner : ProfiledRawJointHybridTwoReplacementOwner A strategy hwin)
    (inputOne : In₁) (inputTwo : In₂) :
    (profiledRawJointHybridMegaLinkedDefaultFrontFrontReceiveMaps A strategy
      hwin controllers initialBank).frontFrontOne
        (profiledRawJointHybridMegaLinkedFrontOneOfShadow A strategy hwin
          controllers initialBank shadow) inputOne
        (profiledRawJointHybridMegaLinkedFrontTwoOfReplacementOwner A strategy
          hwin controllers initialBank owner) inputTwo =
      (default,
        profiledRawJointHybridMegaLinkedTailInitialOne A strategy hwin
          controllers initialBank
            (profiledRawJointHybridShadowPhaseLiveLeftTag A strategy hwin
              shadow.origin shadow.input)) :=
  rfl

@[simp] theorem
    profiledRawJointHybridMegaLinkedDefaultFrontFrontReceiveMaps_leftReplacement_two
    (owner : ProfiledRawJointHybridTwoReplacementOwner A strategy hwin)
    (shadow : OneShadow A strategy hwin)
    (inputTwo : In₂) (inputOne : In₁) :
    (profiledRawJointHybridMegaLinkedDefaultFrontFrontReceiveMaps A strategy
      hwin controllers initialBank).frontFrontTwo
        (profiledRawJointHybridMegaLinkedFrontTwoOfReplacementOwner A strategy
          hwin controllers initialBank owner) inputTwo
        (profiledRawJointHybridMegaLinkedFrontOneOfShadow A strategy hwin
          controllers initialBank shadow) inputOne =
      (default,
        profiledRawJointHybridMegaLinkedTailInitialTwo A strategy hwin
          controllers initialBank
            (profiledRawJointHybridShadowPhaseLiveLeftTag A strategy hwin
              shadow.origin shadow.input)) :=
  rfl

/-- Recognize the genuine process-one common-shadow control. -/
def profiledRawJointHybridMegaLinkedFrontOneShadow?
    (state : OldOne A strategy hwin controllers initialBank) :
    Option (OneShadow A strategy hwin) :=
  match state with
  | .exceptional (.inr (.inr (.inl (.inr (.inl shadow))))) => some shadow
  | _ => none

/-- Process-two shadow mirror. -/
def profiledRawJointHybridMegaLinkedFrontTwoShadow?
    (state : OldTwo A strategy hwin controllers initialBank) :
    Option (TwoShadow A strategy hwin) :=
  match state with
  | .exceptional (.inr (.inr (.inl (.inr (.inl shadow))))) => some shadow
  | _ => none

/-- Recognize the process-one strict-right guard owner delivered to a
process-two shadow. -/
def profiledRawJointHybridMegaLinkedFrontRightGuardOwner?
    (state : OldOne A strategy hwin controllers initialBank) :
    Option (RightGuardOwner A strategy hwin) :=
  match state with
  | .exceptional (.inr (.inr (.inl (.inr (.inr (.inl owner)))))) => some owner
  | _ => none

/-- Recognize the process-two strict-left guard owner delivered to a
process-one shadow. -/
def profiledRawJointHybridMegaLinkedFrontLeftGuardOwner?
    (state : OldTwo A strategy hwin controllers initialBank) :
    Option (LeftGuardOwner A strategy hwin) :=
  match state with
  | .exceptional (.inr (.inr (.inl (.inr (.inr (.inl owner)))))) => some owner
  | _ => none

@[simp] theorem profiledRawJointHybridMegaLinkedFrontOneShadow?_ofShadow
    (shadow : OneShadow A strategy hwin) :
    profiledRawJointHybridMegaLinkedFrontOneShadow? A strategy hwin controllers
        initialBank
        (profiledRawJointHybridMegaLinkedFrontOneOfShadow A strategy hwin
          controllers initialBank shadow) =
      some shadow :=
  rfl

@[simp] theorem profiledRawJointHybridMegaLinkedFrontTwoShadow?_ofShadow
    (shadow : TwoShadow A strategy hwin) :
    profiledRawJointHybridMegaLinkedFrontTwoShadow? A strategy hwin controllers
        initialBank
        (profiledRawJointHybridMegaLinkedFrontTwoOfShadow A strategy hwin
          controllers initialBank shadow) =
      some shadow :=
  rfl

@[simp] theorem
    profiledRawJointHybridMegaLinkedFrontRightGuardOwner?_ofOwner
    (owner : RightGuardOwner A strategy hwin) :
    profiledRawJointHybridMegaLinkedFrontRightGuardOwner? A strategy hwin
        controllers initialBank
        (profiledRawJointHybridMegaLinkedFrontOneOfRightGuardOwner A strategy
          hwin controllers initialBank owner) =
      some owner :=
  rfl

@[simp] theorem
    profiledRawJointHybridMegaLinkedFrontLeftGuardOwner?_ofOwner
    (owner : LeftGuardOwner A strategy hwin) :
    profiledRawJointHybridMegaLinkedFrontLeftGuardOwner? A strategy hwin
        controllers initialBank
        (profiledRawJointHybridMegaLinkedFrontTwoOfLeftGuardOwner A strategy
          hwin controllers initialBank owner) =
      some owner :=
  rfl

/-- The exact process-one handoff row.  Its output is the already verified
shadow/owner output for the current round; its next state is the linked tail
at the direction-selected marked child carried by the freshly computed tag. -/
noncomputable def profiledRawJointHybridMegaLinkedEnterTailOne
    (shadow : OneShadow A strategy hwin)
    (owner : LeftGuardOwner A strategy hwin)
    (ownInput : In₁) (deliveredInput : In₂) :
    Out₁ × OneControl A strategy hwin controllers initialBank :=
  let phase :=
    profiledRawJointHybridOneShadowRecvLeftOwnerPhaseLive A strategy hwin
      shadow owner ownInput deliveredInput
  (phase.1,
    profiledRawJointHybridMegaLinkedTailInitialOne A strategy hwin controllers
      initialBank phase.2.tag)

/-- Process-two strict-right mirror. -/
noncomputable def profiledRawJointHybridMegaLinkedEnterTailTwo
    (shadow : TwoShadow A strategy hwin)
    (owner : RightGuardOwner A strategy hwin)
    (ownInput : In₂) (deliveredInput : In₁) :
    Out₂ × TwoControl A strategy hwin controllers initialBank :=
  let phase :=
    profiledRawJointHybridTwoShadowRecvRightOwnerPhaseLive A strategy hwin
      shadow owner ownInput deliveredInput
  (phase.1,
    profiledRawJointHybridMegaLinkedTailInitialTwo A strategy hwin controllers
      initialBank phase.2.tag)

/-- Complementary process-one row of the strict-right simultaneous handoff.
The delivered process-two shadow determines the same phase-live tag as the
receiver-side row.  Since this is a simultaneous close, the output is the
`closingBoth` coordinate of the very same guarded record used by that
receiver row, not the blind continuation coordinate of its sender label. -/
noncomputable def
    profiledRawJointHybridMegaLinkedEnterTailOneFromRightGuardOwner
    (owner : RightGuardOwner A strategy hwin)
    (shadow : TwoShadow A strategy hwin)
    (ownInput : In₁) (deliveredInput : In₂) :
    Out₁ × OneControl A strategy hwin controllers initialBank :=
  let controller :=
    profiledRawJointHybridShadowRightController A strategy hwin shadow.origin
  let ownerControl :=
    profiledRawJointHybridRightGuardOwnerFor A strategy hwin shadow owner
  let label := controller.labelOf ownerControl
  let output := label.2 shadow.strictReceiver (deliveredInput, ownInput)
  let phase :=
    profiledRawJointHybridTwoShadowRecvRightOwnerPhaseLive A strategy hwin
      shadow owner deliveredInput ownInput
  (pairedRightClosingForRow .both output.physical,
    profiledRawJointHybridMegaLinkedTailInitialOne A strategy hwin controllers
      initialBank phase.2.tag)

/-- Complementary process-two row of the strict-left simultaneous handoff. -/
noncomputable def
    profiledRawJointHybridMegaLinkedEnterTailTwoFromLeftGuardOwner
    (owner : LeftGuardOwner A strategy hwin)
    (shadow : OneShadow A strategy hwin)
    (ownInput : In₂) (deliveredInput : In₁) :
    Out₂ × TwoControl A strategy hwin controllers initialBank :=
  let controller :=
    profiledRawJointHybridShadowLeftController A strategy hwin shadow.origin
  let ownerControl :=
    profiledRawJointHybridLeftGuardOwnerFor A strategy hwin shadow owner
  let label := controller.labelOf ownerControl
  let output := label.2 shadow.strictReceiver (deliveredInput, ownInput)
  let phase :=
    profiledRawJointHybridOneShadowRecvLeftOwnerPhaseLive A strategy hwin
      shadow owner deliveredInput ownInput
  (pairedLeftClosingForRow .both output.physical,
    profiledRawJointHybridMegaLinkedTailInitialTwo A strategy hwin controllers
      initialBank phase.2.tag)

/-- The repaired strict-right handoff emits the literal simultaneous closing
record of the guarded occurrence selected by the delivered shadow. -/
theorem
    profiledRawJointHybridMegaLinkedRightEntry_outputPair_eq_closingBoth
    (owner : RightGuardOwner A strategy hwin)
    (shadow : TwoShadow A strategy hwin)
    (inputOne : In₁) (inputTwo : In₂) :
    let controller :=
      profiledRawJointHybridShadowRightController A strategy hwin shadow.origin
    let ownerControl :=
      profiledRawJointHybridRightGuardOwnerFor A strategy hwin shadow owner
    let output :=
      (controller.labelOf ownerControl).2 shadow.strictReceiver
        (inputTwo, inputOne)
    ((profiledRawJointHybridMegaLinkedEnterTailOneFromRightGuardOwner A
          strategy hwin controllers initialBank owner shadow inputOne
            inputTwo).1,
      (profiledRawJointHybridMegaLinkedEnterTailTwo A strategy hwin controllers
          initialBank shadow owner inputTwo inputOne).1) =
      (pairedRightClosingForRow .both output.physical,
        pairedRightInformedForRow .both output.physical) := by
  rfl

/-- Strict-left mirror of the literal simultaneous-close output equation. -/
theorem
    profiledRawJointHybridMegaLinkedLeftEntry_outputPair_eq_closingBoth
    (shadow : OneShadow A strategy hwin)
    (owner : LeftGuardOwner A strategy hwin)
    (inputOne : In₁) (inputTwo : In₂) :
    let controller :=
      profiledRawJointHybridShadowLeftController A strategy hwin shadow.origin
    let ownerControl :=
      profiledRawJointHybridLeftGuardOwnerFor A strategy hwin shadow owner
    let output :=
      (controller.labelOf ownerControl).2 shadow.strictReceiver
        (inputOne, inputTwo)
    ((profiledRawJointHybridMegaLinkedEnterTailOne A strategy hwin controllers
          initialBank shadow owner inputOne inputTwo).1,
      (profiledRawJointHybridMegaLinkedEnterTailTwoFromLeftGuardOwner A
          strategy hwin controllers initialBank owner shadow inputTwo
            inputOne).1) =
      (pairedLeftInformedForRow .both output.physical,
        pairedLeftClosingForRow .both output.physical) := by
  rfl

/-- The complete strict-right handoff record is exactly the closed candidate
of the guarded right occurrence, evaluated in the `.both` row.  The last
coordinate of `letter` is retained to exhibit the underlying guarded letter;
the simultaneous close correctly replaces that blind coordinate. -/
theorem
    profiledRawJointHybridMegaLinkedRightEntry_roundRecord_eq_targetClose
    (owner : RightGuardOwner A strategy hwin)
    (shadow : TwoShadow A strategy hwin)
    (inputOne : In₁) (inputTwo : In₂) :
    let controller :=
      profiledRawJointHybridShadowRightController A strategy hwin shadow.origin
    let ownerControl :=
      profiledRawJointHybridRightGuardOwnerFor A strategy hwin shadow owner
    let label := controller.labelOf ownerControl
    let output := label.2 shadow.strictReceiver (inputTwo, inputOne)
    let letter : PairedRightBlockLetter
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) :=
      ((inputTwo, inputOne), output.physical, label.1 inputOne)
    bothRoundRecord (inputOne, inputTwo)
        (profiledRawJointHybridMegaLinkedEnterTailOneFromRightGuardOwner A
          strategy hwin controllers initialBank owner shadow inputOne
            inputTwo).1
        (profiledRawJointHybridMegaLinkedEnterTailTwo A strategy hwin controllers
          initialBank shadow owner inputTwo inputOne).1 =
      profiledRawJointTargetRightClosingRecordForMember true .both letter := by
  rfl

/-- Strict-left mirror of the complete guarded close-record equation. -/
theorem
    profiledRawJointHybridMegaLinkedLeftEntry_roundRecord_eq_targetClose
    (shadow : OneShadow A strategy hwin)
    (owner : LeftGuardOwner A strategy hwin)
    (inputOne : In₁) (inputTwo : In₂) :
    let controller :=
      profiledRawJointHybridShadowLeftController A strategy hwin shadow.origin
    let ownerControl :=
      profiledRawJointHybridLeftGuardOwnerFor A strategy hwin shadow owner
    let label := controller.labelOf ownerControl
    let output := label.2 shadow.strictReceiver (inputOne, inputTwo)
    let letter : PairedLeftBlockLetter
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) :=
      ((inputOne, inputTwo), output.physical, label.1 inputTwo)
    bothRoundRecord (inputOne, inputTwo)
        (profiledRawJointHybridMegaLinkedEnterTailOne A strategy hwin controllers
          initialBank shadow owner inputOne inputTwo).1
        (profiledRawJointHybridMegaLinkedEnterTailTwoFromLeftGuardOwner A
          strategy hwin controllers initialBank owner shadow inputTwo
            inputOne).1 =
      profiledRawJointTargetLeftClosingRecordForMember true .both letter := by
  rfl

/-! ### Mixed phase

Only one endpoint knows the tag between its first resolving receive and the
partner's first later receive.  The tagged endpoint nevertheless carries the
complete linked relay.  A repeated receive in the same direction therefore
uses that relay; at the first opposite receive the formerly blind endpoint
imports the delivered tagged relay.  In both cases the missing local control
can be the canonical not-yet-received control of the same tag.  This is a
finite local reconstruction, not a test of the graph or hierarchy side. -/

/-- Process one already carries a tag and receives while process two is still
in the old front. -/
noncomputable def profiledRawJointHybridMegaLinkedTailFrontRecvOne
    (tail : TailOne A strategy hwin) (inputOne : In₁)
    (_front : OldTwo A strategy hwin controllers initialBank)
    (inputTwo : In₂) :
    Out₁ × OneControl A strategy hwin controllers initialBank :=
  let tailController :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartMealyController
      A strategy hwin tail.1
  let next :=
    tailController.recvOne tail.2 inputOne tailController.initialTwo inputTwo
  (next.2,
    profiledRawJointHybridMegaLinkedInjectTailOne A strategy hwin controllers
      initialBank (tail.1, next.1))

/-- Process two already carries a tag and receives while process one remains
in the old front. -/
noncomputable def profiledRawJointHybridMegaLinkedTailFrontRecvTwo
    (tail : TailTwo A strategy hwin) (inputTwo : In₂)
    (_front : OldOne A strategy hwin controllers initialBank)
    (inputOne : In₁) :
    Out₂ × TwoControl A strategy hwin controllers initialBank :=
  let tailController :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartMealyController
      A strategy hwin tail.1
  let next :=
    tailController.recvTwo tail.2 inputTwo tailController.initialOne inputOne
  (next.2,
    profiledRawJointHybridMegaLinkedInjectTailTwo A strategy hwin controllers
      initialBank (tail.1, next.1))

/-- Process one receives a delivered process-two tag for the first time.  Its
own old-front control is deliberately not inspected by the linked step. -/
noncomputable def profiledRawJointHybridMegaLinkedFrontTailRecvOne
    (_front : OldOne A strategy hwin controllers initialBank)
    (inputOne : In₁) (tail : TailTwo A strategy hwin) (inputTwo : In₂) :
    Out₁ × OneControl A strategy hwin controllers initialBank :=
  let tailController :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartMealyController
      A strategy hwin tail.1
  let next :=
    tailController.recvOne tailController.initialOne inputOne tail.2 inputTwo
  (next.2,
    profiledRawJointHybridMegaLinkedInjectTailOne A strategy hwin controllers
      initialBank (tail.1, next.1))

/-- Process-two mirror of first delivered-tag installation. -/
noncomputable def profiledRawJointHybridMegaLinkedFrontTailRecvTwo
    (_front : OldTwo A strategy hwin controllers initialBank)
    (inputTwo : In₂) (tail : TailOne A strategy hwin) (inputOne : In₁) :
    Out₂ × TwoControl A strategy hwin controllers initialBank :=
  let tailController :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartMealyController
      A strategy hwin tail.1
  let next :=
    tailController.recvTwo tailController.initialTwo inputTwo tail.2 inputOne
  (next.2,
    profiledRawJointHybridMegaLinkedInjectTailTwo A strategy hwin controllers
      initialBank (tail.1, next.1))

/-- Expand the minimal two-row front/front interface to the compatibility
six-row table.  The four mixed rows are the canonical local transports and
will also be reinstalled by `...ExactFrontHandoffs`; spelling them out here
makes this constructor independently total. -/
noncomputable def
    profiledRawJointHybridMegaLinkedFrontReceiveMapsOfFrontFront
    (maps : ProfiledRawJointHybridMegaLinkedFrontFrontReceiveMaps A strategy
      hwin controllers initialBank) :
    ProfiledRawJointHybridMegaLinkedFrontReceiveMaps A strategy hwin
      controllers initialBank where
  frontFrontOne := maps.frontFrontOne
  frontFrontTwo := maps.frontFrontTwo
  frontTailOne :=
    profiledRawJointHybridMegaLinkedFrontTailRecvOne A strategy hwin
      controllers initialBank
  frontTailTwo :=
    profiledRawJointHybridMegaLinkedFrontTailRecvTwo A strategy hwin
      controllers initialBank
  tailFrontOne :=
    profiledRawJointHybridMegaLinkedTailFrontRecvOne A strategy hwin
      controllers initialBank
  tailFrontTwo :=
    profiledRawJointHybridMegaLinkedTailFrontRecvTwo A strategy hwin
      controllers initialBank

/-- Replace the four endpoint rows of the two genuine shadow/guard simultaneous
handoffs by their canonical exact-child transitions, and replace all four
mixed rows by their executable linked-tail transports.  Only noncanonical
front/front configurations retain the supplied totalization. -/
noncomputable def profiledRawJointHybridMegaLinkedExactFrontHandoffs
    (fallback : ProfiledRawJointHybridMegaLinkedFrontReceiveMaps A strategy
      hwin controllers initialBank) :
    ProfiledRawJointHybridMegaLinkedFrontReceiveMaps A strategy hwin
      controllers initialBank where
  frontFrontOne := fun one inputOne two inputTwo =>
    match
        profiledRawJointHybridMegaLinkedFrontOneShadow? A strategy hwin
          controllers initialBank one,
        profiledRawJointHybridMegaLinkedFrontLeftGuardOwner? A strategy hwin
          controllers initialBank two with
    | some shadow, some owner =>
        profiledRawJointHybridMegaLinkedEnterTailOne A strategy hwin controllers
          initialBank shadow owner inputOne inputTwo
    | _, _ =>
        match
            profiledRawJointHybridMegaLinkedFrontRightGuardOwner? A strategy
              hwin controllers initialBank one,
            profiledRawJointHybridMegaLinkedFrontTwoShadow? A strategy hwin
              controllers initialBank two with
        | some owner, some shadow =>
            profiledRawJointHybridMegaLinkedEnterTailOneFromRightGuardOwner A
              strategy hwin controllers initialBank owner shadow inputOne
                inputTwo
        | _, _ => fallback.frontFrontOne one inputOne two inputTwo
  frontFrontTwo := fun two inputTwo one inputOne =>
    match
        profiledRawJointHybridMegaLinkedFrontTwoShadow? A strategy hwin
          controllers initialBank two,
        profiledRawJointHybridMegaLinkedFrontRightGuardOwner? A strategy hwin
          controllers initialBank one with
    | some shadow, some owner =>
        profiledRawJointHybridMegaLinkedEnterTailTwo A strategy hwin controllers
          initialBank shadow owner inputTwo inputOne
    | _, _ =>
        match
            profiledRawJointHybridMegaLinkedFrontLeftGuardOwner? A strategy
              hwin controllers initialBank two,
            profiledRawJointHybridMegaLinkedFrontOneShadow? A strategy hwin
              controllers initialBank one with
        | some owner, some shadow =>
            profiledRawJointHybridMegaLinkedEnterTailTwoFromLeftGuardOwner A
              strategy hwin controllers initialBank owner shadow inputTwo
                inputOne
        | _, _ => fallback.frontFrontTwo two inputTwo one inputOne
  frontTailOne :=
    profiledRawJointHybridMegaLinkedFrontTailRecvOne A strategy hwin
      controllers initialBank
  frontTailTwo :=
    profiledRawJointHybridMegaLinkedFrontTailRecvTwo A strategy hwin
      controllers initialBank
  tailFrontOne :=
    profiledRawJointHybridMegaLinkedTailFrontRecvOne A strategy hwin
      controllers initialBank
  tailFrontTwo :=
    profiledRawJointHybridMegaLinkedTailFrontRecvTwo A strategy hwin
      controllers initialBank

@[simp] theorem
    profiledRawJointHybridMegaLinkedExactFrontHandoffs_left_entry
    (fallback : ProfiledRawJointHybridMegaLinkedFrontReceiveMaps A strategy
      hwin controllers initialBank)
    (shadow : OneShadow A strategy hwin)
    (owner : LeftGuardOwner A strategy hwin)
    (inputOne : In₁) (inputTwo : In₂) :
    (profiledRawJointHybridMegaLinkedExactFrontHandoffs A strategy hwin
      controllers initialBank fallback).frontFrontOne
        (.exceptional
          (.inr (.inr (.inl (.inr (.inl shadow)))))) inputOne
        (.exceptional
          (.inr (.inr (.inl (.inr (.inr (.inl owner))))))) inputTwo =
      profiledRawJointHybridMegaLinkedEnterTailOne A strategy hwin controllers
        initialBank shadow owner inputOne inputTwo :=
  rfl

@[simp] theorem
    profiledRawJointHybridMegaLinkedExactFrontHandoffs_right_entry
    (fallback : ProfiledRawJointHybridMegaLinkedFrontReceiveMaps A strategy
      hwin controllers initialBank)
    (shadow : TwoShadow A strategy hwin)
    (owner : RightGuardOwner A strategy hwin)
    (inputTwo : In₂) (inputOne : In₁) :
    (profiledRawJointHybridMegaLinkedExactFrontHandoffs A strategy hwin
      controllers initialBank fallback).frontFrontTwo
        (.exceptional
          (.inr (.inr (.inl (.inr (.inl shadow)))))) inputTwo
        (.exceptional
          (.inr (.inr (.inl (.inr (.inr (.inl owner))))))) inputOne =
      profiledRawJointHybridMegaLinkedEnterTailTwo A strategy hwin controllers
        initialBank shadow owner inputTwo inputOne :=
  rfl

@[simp] theorem
    profiledRawJointHybridMegaLinkedExactFrontHandoffs_right_owner_entry
    (fallback : ProfiledRawJointHybridMegaLinkedFrontReceiveMaps A strategy
      hwin controllers initialBank)
    (owner : RightGuardOwner A strategy hwin)
    (shadow : TwoShadow A strategy hwin)
    (inputOne : In₁) (inputTwo : In₂) :
    (profiledRawJointHybridMegaLinkedExactFrontHandoffs A strategy hwin
      controllers initialBank fallback).frontFrontOne
        (profiledRawJointHybridMegaLinkedFrontOneOfRightGuardOwner A strategy
          hwin controllers initialBank owner) inputOne
        (profiledRawJointHybridMegaLinkedFrontTwoOfShadow A strategy hwin
          controllers initialBank shadow) inputTwo =
      profiledRawJointHybridMegaLinkedEnterTailOneFromRightGuardOwner A strategy
        hwin controllers initialBank owner shadow inputOne inputTwo :=
  rfl

@[simp] theorem
    profiledRawJointHybridMegaLinkedExactFrontHandoffs_left_owner_entry
    (fallback : ProfiledRawJointHybridMegaLinkedFrontReceiveMaps A strategy
      hwin controllers initialBank)
    (owner : LeftGuardOwner A strategy hwin)
    (shadow : OneShadow A strategy hwin)
    (inputTwo : In₂) (inputOne : In₁) :
    (profiledRawJointHybridMegaLinkedExactFrontHandoffs A strategy hwin
      controllers initialBank fallback).frontFrontTwo
        (profiledRawJointHybridMegaLinkedFrontTwoOfLeftGuardOwner A strategy
          hwin controllers initialBank owner) inputTwo
        (profiledRawJointHybridMegaLinkedFrontOneOfShadow A strategy hwin
          controllers initialBank shadow) inputOne =
      profiledRawJointHybridMegaLinkedEnterTailTwoFromLeftGuardOwner A strategy
        hwin controllers initialBank owner shadow inputTwo inputOne :=
  rfl

@[simp] theorem
    profiledRawJointHybridMegaLinkedExactFrontHandoffs_frontTailOne
    (fallback : ProfiledRawJointHybridMegaLinkedFrontReceiveMaps A strategy
      hwin controllers initialBank)
    (front : OldOne A strategy hwin controllers initialBank)
    (inputOne : In₁) (tail : TailTwo A strategy hwin) (inputTwo : In₂) :
    (profiledRawJointHybridMegaLinkedExactFrontHandoffs A strategy hwin
      controllers initialBank fallback).frontTailOne front inputOne tail
        inputTwo =
      profiledRawJointHybridMegaLinkedFrontTailRecvOne A strategy hwin
        controllers initialBank front inputOne tail inputTwo :=
  rfl

@[simp] theorem
    profiledRawJointHybridMegaLinkedExactFrontHandoffs_frontTailTwo
    (fallback : ProfiledRawJointHybridMegaLinkedFrontReceiveMaps A strategy
      hwin controllers initialBank)
    (front : OldTwo A strategy hwin controllers initialBank)
    (inputTwo : In₂) (tail : TailOne A strategy hwin) (inputOne : In₁) :
    (profiledRawJointHybridMegaLinkedExactFrontHandoffs A strategy hwin
      controllers initialBank fallback).frontTailTwo front inputTwo tail
        inputOne =
      profiledRawJointHybridMegaLinkedFrontTailRecvTwo A strategy hwin
        controllers initialBank front inputTwo tail inputOne :=
  rfl

@[simp] theorem
    profiledRawJointHybridMegaLinkedExactFrontHandoffs_tailFrontOne
    (fallback : ProfiledRawJointHybridMegaLinkedFrontReceiveMaps A strategy
      hwin controllers initialBank)
    (tail : TailOne A strategy hwin) (inputOne : In₁)
    (front : OldTwo A strategy hwin controllers initialBank)
    (inputTwo : In₂) :
    (profiledRawJointHybridMegaLinkedExactFrontHandoffs A strategy hwin
      controllers initialBank fallback).tailFrontOne tail inputOne front
        inputTwo =
      profiledRawJointHybridMegaLinkedTailFrontRecvOne A strategy hwin
        controllers initialBank tail inputOne front inputTwo :=
  rfl

@[simp] theorem
    profiledRawJointHybridMegaLinkedExactFrontHandoffs_tailFrontTwo
    (fallback : ProfiledRawJointHybridMegaLinkedFrontReceiveMaps A strategy
      hwin controllers initialBank)
    (tail : TailTwo A strategy hwin) (inputTwo : In₂)
    (front : OldOne A strategy hwin controllers initialBank)
    (inputOne : In₁) :
    (profiledRawJointHybridMegaLinkedExactFrontHandoffs A strategy hwin
      controllers initialBank fallback).tailFrontTwo tail inputTwo front
        inputOne =
      profiledRawJointHybridMegaLinkedTailFrontRecvTwo A strategy hwin
        controllers initialBank tail inputTwo front inputOne :=
  rfl

/-! ## Fully executable maps outside the receive seam -/

noncomputable def profiledRawJointHybridMegaLinkedInitialNoRecvOne
    (_ : Unit) (input : In₁) :
    Out₁ × OneControl A strategy hwin controllers initialBank :=
  let next := stepProfiledRawJointRootRightOwner A strategy controllers
    (profiledRawJointInitialRightOwnerInitial A strategy controllers) input
  (next.1,
    profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin controllers
      initialBank (.exceptional
        (profiledRawJointHybridMegaExceptionalOneOfOld A strategy hwin
          controllers initialBank (.inl next.2))))

noncomputable def profiledRawJointHybridMegaLinkedInitialNoRecvTwo
    (_ : Unit) (input : In₂) :
    Out₂ × TwoControl A strategy hwin controllers initialBank :=
  let next := stepProfiledRawJointRootLeftOwner A strategy controllers
    (profiledRawJointInitialLeftOwnerInitial A strategy controllers) input
  (next.1,
    profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin controllers
      initialBank (.exceptional
        (profiledRawJointHybridMegaExceptionalTwoOfOld A strategy hwin
          controllers initialBank (.inr (.inl next.2)))))

noncomputable def profiledRawJointHybridMegaLinkedExceptionalNoRecvOne
    (state : ExceptionalOne A strategy hwin controllers initialBank)
    (input : In₁) :
    Out₁ × OneControl A strategy hwin controllers initialBank :=
  match state with
  | .inl front =>
      let next := profiledRawJointHybridMegaExceptionalNoRecvOne A strategy
        hwin controllers initialBank front input
      (next.1,
        profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin controllers
          initialBank next.2)
  | .inr tail =>
      let next :=
        FiniteAcknowledgedDelayedCarrier.noRecvMealy
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvOne
            A strategy hwin) tail.2 input
      (next.2,
        profiledRawJointHybridMegaLinkedInjectTailOne A strategy hwin
          controllers initialBank (tail.1, next.1))

noncomputable def profiledRawJointHybridMegaLinkedExceptionalNoRecvTwo
    (state : ExceptionalTwo A strategy hwin controllers initialBank)
    (input : In₂) :
    Out₂ × TwoControl A strategy hwin controllers initialBank :=
  match state with
  | .inl front =>
      let next := profiledRawJointHybridMegaExceptionalNoRecvTwo A strategy
        hwin controllers initialBank front input
      (next.1,
        profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin controllers
          initialBank next.2)
  | .inr tail =>
      let next :=
        FiniteAcknowledgedDelayedCarrier.noRecvMealy
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvTwo
            A strategy hwin) tail.2 input
      (next.2,
        profiledRawJointHybridMegaLinkedInjectTailTwo A strategy hwin
          controllers initialBank (tail.1, next.1))

/-! ## Receive dispatch and complete indexed adapter -/

noncomputable def profiledRawJointHybridMegaLinkedOtherRecvOne
    (_fallbackTag : RetainedTag A strategy hwin)
    (maps : ProfiledRawJointHybridMegaLinkedFrontReceiveMaps A strategy hwin
      controllers initialBank)
    (one : OneControl A strategy hwin controllers initialBank) (inputOne : In₁)
    (two : TwoControl A strategy hwin controllers initialBank) (inputTwo : In₂) :
    Out₁ × OneControl A strategy hwin controllers initialBank := by
  let oneView := profiledRawJointHybridMegaLinkedOneView A strategy hwin
    controllers initialBank one
  let twoView := profiledRawJointHybridMegaLinkedTwoView A strategy hwin
    controllers initialBank two
  match oneView, twoView with
  | .front (.initial _), .front (.initial _) =>
      let next := profiledRawJointHybridInitialRootRecvOne A strategy hwin
        controllers (inputOne, inputTwo)
      exact (next.1,
        profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin controllers
          initialBank (.exceptional
            (profiledRawJointHybridMegaExceptionalOneOfInitialShadow A strategy
              hwin controllers initialBank next.2)))
  | .front frontOne, .front frontTwo =>
      exact maps.frontFrontOne frontOne inputOne frontTwo inputTwo
  | .front frontOne, .tail tailTwo =>
      exact maps.frontTailOne frontOne inputOne tailTwo inputTwo
  | .tail tailOne, .front frontTwo =>
      exact maps.tailFrontOne tailOne inputOne frontTwo inputTwo
  | .tail tailOne, .tail tailTwo =>
      let tailController :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartMealyController
          A strategy hwin tailOne.1
      let next := tailController.recvOne tailOne.2 inputOne tailTwo.2 inputTwo
      exact (next.2,
        profiledRawJointHybridMegaLinkedInjectTailOne A strategy hwin
          controllers initialBank (tailOne.1, next.1))

noncomputable def profiledRawJointHybridMegaLinkedOtherRecvTwo
    (_fallbackTag : RetainedTag A strategy hwin)
    (maps : ProfiledRawJointHybridMegaLinkedFrontReceiveMaps A strategy hwin
      controllers initialBank)
    (two : TwoControl A strategy hwin controllers initialBank) (inputTwo : In₂)
    (one : OneControl A strategy hwin controllers initialBank) (inputOne : In₁) :
    Out₂ × TwoControl A strategy hwin controllers initialBank := by
  let oneView := profiledRawJointHybridMegaLinkedOneView A strategy hwin
    controllers initialBank one
  let twoView := profiledRawJointHybridMegaLinkedTwoView A strategy hwin
    controllers initialBank two
  match twoView, oneView with
  | .front (.initial _), .front (.initial _) =>
      let next := profiledRawJointHybridInitialRootRecvTwo A strategy hwin
        controllers (inputOne, inputTwo)
      exact (next.1,
        profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin controllers
          initialBank (.exceptional
            (profiledRawJointHybridMegaExceptionalTwoOfInitialShadow A strategy
              hwin controllers initialBank next.2)))
  | .front frontTwo, .front frontOne =>
      exact maps.frontFrontTwo frontTwo inputTwo frontOne inputOne
  | .front frontTwo, .tail tailOne =>
      exact maps.frontTailTwo frontTwo inputTwo tailOne inputOne
  | .tail tailTwo, .front frontOne =>
      exact maps.tailFrontTwo tailTwo inputTwo frontOne inputOne
  | .tail tailTwo, .tail tailOne =>
      let tailController :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartMealyController
          A strategy hwin tailTwo.1
      let next := tailController.recvTwo tailTwo.2 inputTwo tailOne.2 inputOne
      exact (next.2,
        profiledRawJointHybridMegaLinkedInjectTailTwo A strategy hwin
          controllers initialBank (tailTwo.1, next.1))

/-! ## Closed tail equations

These equations are the executable suffix boundary.  Once both delivered
controls carry the linked tail, neither endpoint can return to the mega
front.  The transition is literally the already verified acknowledged
controller transition. -/

@[simp] theorem profiledRawJointHybridMegaLinkedExceptionalNoRecvOne_tail
    (tail : TailOne A strategy hwin) (input : In₁) :
    profiledRawJointHybridMegaLinkedExceptionalNoRecvOne A strategy hwin
        controllers initialBank (.inr tail) input =
      let next :=
        FiniteAcknowledgedDelayedCarrier.noRecvMealy
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvOne
            A strategy hwin) tail.2 input
      (next.2,
        profiledRawJointHybridMegaLinkedInjectTailOne A strategy hwin
          controllers initialBank (tail.1, next.1)) :=
  rfl

@[simp] theorem profiledRawJointHybridMegaLinkedExceptionalNoRecvTwo_tail
    (tail : TailTwo A strategy hwin) (input : In₂) :
    profiledRawJointHybridMegaLinkedExceptionalNoRecvTwo A strategy hwin
        controllers initialBank (.inr tail) input =
      let next :=
        FiniteAcknowledgedDelayedCarrier.noRecvMealy
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvTwo
            A strategy hwin) tail.2 input
      (next.2,
        profiledRawJointHybridMegaLinkedInjectTailTwo A strategy hwin
          controllers initialBank (tail.1, next.1)) :=
  rfl

@[simp] theorem profiledRawJointHybridMegaLinkedOtherRecvOne_tail_tail
    (fallbackTag : RetainedTag A strategy hwin)
    (maps : ProfiledRawJointHybridMegaLinkedFrontReceiveMaps A strategy hwin
      controllers initialBank)
    (one : TailOne A strategy hwin) (inputOne : In₁)
    (two : TailTwo A strategy hwin) (inputTwo : In₂) :
    profiledRawJointHybridMegaLinkedOtherRecvOne A strategy hwin controllers
        initialBank fallbackTag maps
        (profiledRawJointHybridMegaLinkedInjectTailOne A strategy hwin
          controllers initialBank one) inputOne
        (profiledRawJointHybridMegaLinkedInjectTailTwo A strategy hwin
          controllers initialBank two) inputTwo =
      let tailController :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartMealyController
          A strategy hwin one.1
      let next := tailController.recvOne one.2 inputOne two.2 inputTwo
      (next.2,
        profiledRawJointHybridMegaLinkedInjectTailOne A strategy hwin
          controllers initialBank (one.1, next.1)) :=
  rfl

@[simp] theorem profiledRawJointHybridMegaLinkedOtherRecvTwo_tail_tail
    (fallbackTag : RetainedTag A strategy hwin)
    (maps : ProfiledRawJointHybridMegaLinkedFrontReceiveMaps A strategy hwin
      controllers initialBank)
    (two : TailTwo A strategy hwin) (inputTwo : In₂)
    (one : TailOne A strategy hwin) (inputOne : In₁) :
    profiledRawJointHybridMegaLinkedOtherRecvTwo A strategy hwin controllers
        initialBank fallbackTag maps
        (profiledRawJointHybridMegaLinkedInjectTailTwo A strategy hwin
          controllers initialBank two) inputTwo
        (profiledRawJointHybridMegaLinkedInjectTailOne A strategy hwin
          controllers initialBank one) inputOne =
      let tailController :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartMealyController
          A strategy hwin two.1
      let next := tailController.recvTwo two.2 inputTwo one.2 inputOne
      (next.2,
        profiledRawJointHybridMegaLinkedInjectTailTwo A strategy hwin
          controllers initialBank (two.1, next.1)) :=
  rfl

/-- Compatibility constructor from a six-field total table.  The four mixed
fields are ignored by the exact override, so only its two front/front fields
remain observationally relevant. -/
noncomputable def profiledRawJointHybridMegaLinkedExceptionalAdapter
    (fallbackTag : RetainedTag A strategy hwin)
    (maps : ProfiledRawJointHybridMegaLinkedFrontReceiveMaps A strategy hwin
      controllers initialBank) :
    ProfiledRawJointHybridMegaExceptionalAdapter A strategy hwin initialBank
      Unit Unit
      (ExceptionalOne A strategy hwin controllers initialBank)
      (ExceptionalTwo A strategy hwin controllers initialBank) where
  initialOne := ()
  initialTwo := ()
  initialOutputOne := default
  initialOutputTwo := default
  initialNoRecvOne :=
    profiledRawJointHybridMegaLinkedInitialNoRecvOne A strategy hwin
      controllers initialBank
  exceptionalNoRecvOne :=
    profiledRawJointHybridMegaLinkedExceptionalNoRecvOne A strategy hwin
      controllers initialBank
  initialNoRecvTwo :=
    profiledRawJointHybridMegaLinkedInitialNoRecvTwo A strategy hwin
      controllers initialBank
  exceptionalNoRecvTwo :=
    profiledRawJointHybridMegaLinkedExceptionalNoRecvTwo A strategy hwin
      controllers initialBank
  otherRecvOne :=
    profiledRawJointHybridMegaLinkedOtherRecvOne A strategy hwin controllers
      initialBank fallbackTag
        (profiledRawJointHybridMegaLinkedExactFrontHandoffs A strategy hwin
          controllers initialBank maps)
  otherRecvTwo :=
    profiledRawJointHybridMegaLinkedOtherRecvTwo A strategy hwin controllers
      initialBank fallbackTag
        (profiledRawJointHybridMegaLinkedExactFrontHandoffs A strategy hwin
          controllers initialBank maps)

/-- Public minimal constructor: the caller supplies only the two residual
front/front rows.  Genuine entry, mixed transport, tail/tail receives, and all
non-receives are fixed by the adapter. -/
noncomputable def
    profiledRawJointHybridMegaLinkedExceptionalAdapterOfFrontFront
    (fallbackTag : RetainedTag A strategy hwin)
    (maps : ProfiledRawJointHybridMegaLinkedFrontFrontReceiveMaps A strategy
      hwin controllers initialBank) :=
  profiledRawJointHybridMegaLinkedExceptionalAdapter A strategy hwin
    controllers initialBank fallbackTag
      (profiledRawJointHybridMegaLinkedFrontReceiveMapsOfFrontFront A strategy
        hwin controllers initialBank maps)

/-- Closed operational adapter.  Its only arbitrary-looking rows are the
explicit local defaults above; every root, genuine handoff, mixed, and tail
row remains the canonical construction.  “Unconditional” here concerns the
transition table: it adds no semantic or acceptance hypothesis. -/
noncomputable def
    profiledRawJointHybridMegaLinkedUnconditionalExceptionalAdapter
    (fallbackTag : RetainedTag A strategy hwin) :=
  profiledRawJointHybridMegaLinkedExceptionalAdapterOfFrontFront A strategy
    hwin controllers initialBank fallbackTag
      (profiledRawJointHybridMegaLinkedDefaultFrontFrontReceiveMaps A strategy
        hwin controllers initialBank)

/-! The four endpoint rows of the two real common-shadow simultaneous entries
are now theorems, not obligations on `maps`. -/

@[simp] theorem
    profiledRawJointHybridMegaLinkedExceptionalAdapter_left_entry
    (fallbackTag : RetainedTag A strategy hwin)
    (maps : ProfiledRawJointHybridMegaLinkedFrontReceiveMaps A strategy hwin
      controllers initialBank)
    (shadow : OneShadow A strategy hwin)
    (owner : LeftGuardOwner A strategy hwin)
    (inputOne : In₁) (inputTwo : In₂) :
    (profiledRawJointHybridMegaLinkedExceptionalAdapter A strategy hwin
      controllers initialBank fallbackTag maps).otherRecvOne
        (profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin controllers
          initialBank
          (profiledRawJointHybridMegaLinkedFrontOneOfShadow A strategy hwin
            controllers initialBank shadow)) inputOne
        (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin controllers
          initialBank
          (profiledRawJointHybridMegaLinkedFrontTwoOfLeftGuardOwner A strategy
            hwin controllers initialBank owner)) inputTwo =
      profiledRawJointHybridMegaLinkedEnterTailOne A strategy hwin controllers
        initialBank shadow owner inputOne inputTwo :=
  rfl

@[simp] theorem
    profiledRawJointHybridMegaLinkedExceptionalAdapter_right_entry
    (fallbackTag : RetainedTag A strategy hwin)
    (maps : ProfiledRawJointHybridMegaLinkedFrontReceiveMaps A strategy hwin
      controllers initialBank)
    (shadow : TwoShadow A strategy hwin)
    (owner : RightGuardOwner A strategy hwin)
    (inputTwo : In₂) (inputOne : In₁) :
    (profiledRawJointHybridMegaLinkedExceptionalAdapter A strategy hwin
      controllers initialBank fallbackTag maps).otherRecvTwo
        (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin controllers
          initialBank
          (profiledRawJointHybridMegaLinkedFrontTwoOfShadow A strategy hwin
            controllers initialBank shadow)) inputTwo
        (profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin controllers
          initialBank
          (profiledRawJointHybridMegaLinkedFrontOneOfRightGuardOwner A strategy
            hwin controllers initialBank owner)) inputOne =
      profiledRawJointHybridMegaLinkedEnterTailTwo A strategy hwin controllers
        initialBank shadow owner inputTwo inputOne :=
  rfl

/-- The owner endpoint of the same strict-right simultaneous handoff is also
internal to the adapter.  It reads the delivered shadow and installs the same
marked child as the shadow-receiver endpoint above. -/
@[simp] theorem
    profiledRawJointHybridMegaLinkedExceptionalAdapter_right_owner_entry
    (fallbackTag : RetainedTag A strategy hwin)
    (maps : ProfiledRawJointHybridMegaLinkedFrontReceiveMaps A strategy hwin
      controllers initialBank)
    (owner : RightGuardOwner A strategy hwin)
    (shadow : TwoShadow A strategy hwin)
    (inputOne : In₁) (inputTwo : In₂) :
    (profiledRawJointHybridMegaLinkedExceptionalAdapter A strategy hwin
      controllers initialBank fallbackTag maps).otherRecvOne
        (profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin controllers
          initialBank
          (profiledRawJointHybridMegaLinkedFrontOneOfRightGuardOwner A strategy
            hwin controllers initialBank owner)) inputOne
        (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin controllers
          initialBank
          (profiledRawJointHybridMegaLinkedFrontTwoOfShadow A strategy hwin
            controllers initialBank shadow)) inputTwo =
      profiledRawJointHybridMegaLinkedEnterTailOneFromRightGuardOwner A strategy
        hwin controllers initialBank owner shadow inputOne inputTwo :=
  rfl

/-- Strict-left mirror of the complementary owner endpoint. -/
@[simp] theorem
    profiledRawJointHybridMegaLinkedExceptionalAdapter_left_owner_entry
    (fallbackTag : RetainedTag A strategy hwin)
    (maps : ProfiledRawJointHybridMegaLinkedFrontReceiveMaps A strategy hwin
      controllers initialBank)
    (owner : LeftGuardOwner A strategy hwin)
    (shadow : OneShadow A strategy hwin)
    (inputTwo : In₂) (inputOne : In₁) :
    (profiledRawJointHybridMegaLinkedExceptionalAdapter A strategy hwin
      controllers initialBank fallbackTag maps).otherRecvTwo
        (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin controllers
          initialBank
          (profiledRawJointHybridMegaLinkedFrontTwoOfLeftGuardOwner A strategy
            hwin controllers initialBank owner)) inputTwo
        (profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin controllers
          initialBank
          (profiledRawJointHybridMegaLinkedFrontOneOfShadow A strategy hwin
            controllers initialBank shadow)) inputOne =
      profiledRawJointHybridMegaLinkedEnterTailTwoFromLeftGuardOwner A strategy
        hwin controllers initialBank owner shadow inputTwo inputOne :=
  rfl

/-! The closed/default instance preserves every reachable entry row.  These
specializations make that fact available without unfolding the totalization. -/

@[simp] theorem
    profiledRawJointHybridMegaLinkedUnconditionalExceptionalAdapter_root_one
    (fallbackTag : RetainedTag A strategy hwin)
    (inputOne : In₁) (inputTwo : In₂) :
    (profiledRawJointHybridMegaLinkedUnconditionalExceptionalAdapter A strategy
      hwin controllers initialBank fallbackTag).otherRecvOne
        (.initial ()) inputOne (.initial ()) inputTwo =
      let next := profiledRawJointHybridInitialRootRecvOne A strategy hwin
        controllers (inputOne, inputTwo)
      (next.1,
        profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin controllers
          initialBank (.exceptional
            (profiledRawJointHybridMegaExceptionalOneOfInitialShadow A strategy
              hwin controllers initialBank next.2))) :=
  rfl

@[simp] theorem
    profiledRawJointHybridMegaLinkedUnconditionalExceptionalAdapter_root_two
    (fallbackTag : RetainedTag A strategy hwin)
    (inputTwo : In₂) (inputOne : In₁) :
    (profiledRawJointHybridMegaLinkedUnconditionalExceptionalAdapter A strategy
      hwin controllers initialBank fallbackTag).otherRecvTwo
        (.initial ()) inputTwo (.initial ()) inputOne =
      let next := profiledRawJointHybridInitialRootRecvTwo A strategy hwin
        controllers (inputOne, inputTwo)
      (next.1,
        profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin controllers
          initialBank (.exceptional
            (profiledRawJointHybridMegaExceptionalTwoOfInitialShadow A strategy
              hwin controllers initialBank next.2))) :=
  rfl

@[simp] theorem
    profiledRawJointHybridMegaLinkedUnconditionalExceptionalAdapter_initialShadows_one
    (fallbackTag : RetainedTag A strategy hwin)
    (shadowOne : ProfiledRawJointHybridInitialOneShadow A strategy hwin
      controllers)
    (shadowTwo : ProfiledRawJointHybridInitialTwoShadow A strategy hwin
      controllers)
    (inputOne : In₁) (inputTwo : In₂) :
    (profiledRawJointHybridMegaLinkedUnconditionalExceptionalAdapter A strategy
      hwin controllers initialBank fallbackTag).otherRecvOne
        (profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin controllers
          initialBank (.exceptional
            (profiledRawJointHybridMegaExceptionalOneOfInitialShadow A strategy
              hwin controllers initialBank shadowOne))) inputOne
        (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin controllers
          initialBank (.exceptional
            (profiledRawJointHybridMegaExceptionalTwoOfInitialShadow A strategy
              hwin controllers initialBank shadowTwo))) inputTwo =
      let next := profiledRawJointHybridMegaInitialToCoupledOne A strategy hwin
        controllers shadowTwo inputOne inputTwo
      (next.1,
        profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin controllers
          initialBank (.exceptional
            (profiledRawJointHybridMegaExceptionalOneOfPinnedInitial A strategy
              hwin controllers initialBank (.inr (.inl next.2))))) :=
  rfl

@[simp] theorem
    profiledRawJointHybridMegaLinkedUnconditionalExceptionalAdapter_initialShadows_two
    (fallbackTag : RetainedTag A strategy hwin)
    (shadowTwo : ProfiledRawJointHybridInitialTwoShadow A strategy hwin
      controllers)
    (shadowOne : ProfiledRawJointHybridInitialOneShadow A strategy hwin
      controllers)
    (inputTwo : In₂) (inputOne : In₁) :
    (profiledRawJointHybridMegaLinkedUnconditionalExceptionalAdapter A strategy
      hwin controllers initialBank fallbackTag).otherRecvTwo
        (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin controllers
          initialBank (.exceptional
            (profiledRawJointHybridMegaExceptionalTwoOfInitialShadow A strategy
              hwin controllers initialBank shadowTwo))) inputTwo
        (profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin controllers
          initialBank (.exceptional
            (profiledRawJointHybridMegaExceptionalOneOfInitialShadow A strategy
              hwin controllers initialBank shadowOne))) inputOne =
      let next := profiledRawJointHybridMegaInitialToCoupledTwo A strategy hwin
        controllers shadowOne inputTwo inputOne
      (next.1,
        profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin controllers
          initialBank (.exceptional
            (profiledRawJointHybridMegaExceptionalTwoOfPinnedInitial A strategy
              hwin controllers initialBank (.inr (.inl next.2))))) :=
  rfl

@[simp] theorem
    profiledRawJointHybridMegaLinkedUnconditionalExceptionalAdapter_common_one
    (fallbackTag : RetainedTag A strategy hwin)
    (commonOne commonTwo :
      ProfiledRawJointHybridCommonControl A strategy hwin)
    (inputOne : In₁) (inputTwo : In₂) :
    (profiledRawJointHybridMegaLinkedUnconditionalExceptionalAdapter A strategy
      hwin controllers initialBank fallbackTag).otherRecvOne
        (profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin controllers
          initialBank
            (profiledRawJointHybridMegaLinkedFrontOneOfCommon A strategy hwin
              controllers initialBank commonOne)) inputOne
        (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin controllers
          initialBank
            (profiledRawJointHybridMegaLinkedFrontTwoOfCommon A strategy hwin
              controllers initialBank commonTwo)) inputTwo =
      let next := profiledRawJointHybridCommonToOneShadow A strategy hwin
        commonOne inputOne inputTwo
      (next.1,
        profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin controllers
          initialBank
            (profiledRawJointHybridMegaLinkedFrontOneOfShadow A strategy hwin
              controllers initialBank next.2)) :=
  rfl

@[simp] theorem
    profiledRawJointHybridMegaLinkedUnconditionalExceptionalAdapter_common_two
    (fallbackTag : RetainedTag A strategy hwin)
    (commonTwo commonOne :
      ProfiledRawJointHybridCommonControl A strategy hwin)
    (inputTwo : In₂) (inputOne : In₁) :
    (profiledRawJointHybridMegaLinkedUnconditionalExceptionalAdapter A strategy
      hwin controllers initialBank fallbackTag).otherRecvTwo
        (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin controllers
          initialBank
            (profiledRawJointHybridMegaLinkedFrontTwoOfCommon A strategy hwin
              controllers initialBank commonTwo)) inputTwo
        (profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin controllers
          initialBank
            (profiledRawJointHybridMegaLinkedFrontOneOfCommon A strategy hwin
              controllers initialBank commonOne)) inputOne =
      let next := profiledRawJointHybridCommonToTwoShadow A strategy hwin
        commonTwo inputTwo inputOne
      (next.1,
        profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin controllers
          initialBank
            (profiledRawJointHybridMegaLinkedFrontTwoOfShadow A strategy hwin
              controllers initialBank next.2)) :=
  rfl

@[simp] theorem
    profiledRawJointHybridMegaLinkedUnconditionalExceptionalAdapter_shadows_one
    (fallbackTag : RetainedTag A strategy hwin)
    (shadowOne : OneShadow A strategy hwin)
    (shadowTwo : TwoShadow A strategy hwin)
    (inputOne : In₁) (inputTwo : In₂) :
    (profiledRawJointHybridMegaLinkedUnconditionalExceptionalAdapter A strategy
      hwin controllers initialBank fallbackTag).otherRecvOne
        (profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin controllers
          initialBank
            (profiledRawJointHybridMegaLinkedFrontOneOfShadow A strategy hwin
              controllers initialBank shadowOne)) inputOne
        (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin controllers
          initialBank
            (profiledRawJointHybridMegaLinkedFrontTwoOfShadow A strategy hwin
              controllers initialBank shadowTwo)) inputTwo =
      let next := profiledRawJointHybridOneShadowRecvCommon A strategy hwin
        shadowOne shadowTwo inputOne inputTwo
      (next.1,
        profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin controllers
          initialBank
            (profiledRawJointHybridMegaLinkedFrontOneOfShadow A strategy hwin
              controllers initialBank next.2)) :=
  rfl

@[simp] theorem
    profiledRawJointHybridMegaLinkedUnconditionalExceptionalAdapter_shadows_two
    (fallbackTag : RetainedTag A strategy hwin)
    (shadowTwo : TwoShadow A strategy hwin)
    (shadowOne : OneShadow A strategy hwin)
    (inputTwo : In₂) (inputOne : In₁) :
    (profiledRawJointHybridMegaLinkedUnconditionalExceptionalAdapter A strategy
      hwin controllers initialBank fallbackTag).otherRecvTwo
        (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin controllers
          initialBank
            (profiledRawJointHybridMegaLinkedFrontTwoOfShadow A strategy hwin
              controllers initialBank shadowTwo)) inputTwo
        (profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin controllers
          initialBank
            (profiledRawJointHybridMegaLinkedFrontOneOfShadow A strategy hwin
              controllers initialBank shadowOne)) inputOne =
      let next := profiledRawJointHybridTwoShadowRecvCommon A strategy hwin
        shadowTwo shadowOne inputTwo inputOne
      (next.1,
        profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin controllers
          initialBank
            (profiledRawJointHybridMegaLinkedFrontTwoOfShadow A strategy hwin
              controllers initialBank next.2)) :=
  rfl

@[simp] theorem
    profiledRawJointHybridMegaLinkedUnconditionalExceptionalAdapter_rightReplacement_one
    (fallbackTag : RetainedTag A strategy hwin)
    (owner : ProfiledRawJointHybridOneReplacementOwner A strategy hwin)
    (shadow : TwoShadow A strategy hwin)
    (inputOne : In₁) (inputTwo : In₂) :
    (profiledRawJointHybridMegaLinkedUnconditionalExceptionalAdapter A strategy
      hwin controllers initialBank fallbackTag).otherRecvOne
        (profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin controllers
          initialBank
            (profiledRawJointHybridMegaLinkedFrontOneOfReplacementOwner A
              strategy hwin controllers initialBank owner)) inputOne
        (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin controllers
          initialBank
            (profiledRawJointHybridMegaLinkedFrontTwoOfShadow A strategy hwin
              controllers initialBank shadow)) inputTwo =
      (default,
        profiledRawJointHybridMegaLinkedTailInitialOne A strategy hwin
          controllers initialBank
            (profiledRawJointHybridShadowPhaseLiveRightTag A strategy hwin
              shadow.origin shadow.input)) :=
  rfl

@[simp] theorem
    profiledRawJointHybridMegaLinkedUnconditionalExceptionalAdapter_rightReplacement_two
    (fallbackTag : RetainedTag A strategy hwin)
    (shadow : TwoShadow A strategy hwin)
    (owner : ProfiledRawJointHybridOneReplacementOwner A strategy hwin)
    (inputTwo : In₂) (inputOne : In₁) :
    (profiledRawJointHybridMegaLinkedUnconditionalExceptionalAdapter A strategy
      hwin controllers initialBank fallbackTag).otherRecvTwo
        (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin controllers
          initialBank
            (profiledRawJointHybridMegaLinkedFrontTwoOfShadow A strategy hwin
              controllers initialBank shadow)) inputTwo
        (profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin controllers
          initialBank
            (profiledRawJointHybridMegaLinkedFrontOneOfReplacementOwner A
              strategy hwin controllers initialBank owner)) inputOne =
      (default,
        profiledRawJointHybridMegaLinkedTailInitialTwo A strategy hwin
          controllers initialBank
            (profiledRawJointHybridShadowPhaseLiveRightTag A strategy hwin
              shadow.origin shadow.input)) :=
  rfl

@[simp] theorem
    profiledRawJointHybridMegaLinkedUnconditionalExceptionalAdapter_leftReplacement_one
    (fallbackTag : RetainedTag A strategy hwin)
    (shadow : OneShadow A strategy hwin)
    (owner : ProfiledRawJointHybridTwoReplacementOwner A strategy hwin)
    (inputOne : In₁) (inputTwo : In₂) :
    (profiledRawJointHybridMegaLinkedUnconditionalExceptionalAdapter A strategy
      hwin controllers initialBank fallbackTag).otherRecvOne
        (profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin controllers
          initialBank
            (profiledRawJointHybridMegaLinkedFrontOneOfShadow A strategy hwin
              controllers initialBank shadow)) inputOne
        (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin controllers
          initialBank
            (profiledRawJointHybridMegaLinkedFrontTwoOfReplacementOwner A
              strategy hwin controllers initialBank owner)) inputTwo =
      (default,
        profiledRawJointHybridMegaLinkedTailInitialOne A strategy hwin
          controllers initialBank
            (profiledRawJointHybridShadowPhaseLiveLeftTag A strategy hwin
              shadow.origin shadow.input)) :=
  rfl

@[simp] theorem
    profiledRawJointHybridMegaLinkedUnconditionalExceptionalAdapter_leftReplacement_two
    (fallbackTag : RetainedTag A strategy hwin)
    (owner : ProfiledRawJointHybridTwoReplacementOwner A strategy hwin)
    (shadow : OneShadow A strategy hwin)
    (inputTwo : In₂) (inputOne : In₁) :
    (profiledRawJointHybridMegaLinkedUnconditionalExceptionalAdapter A strategy
      hwin controllers initialBank fallbackTag).otherRecvTwo
        (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin controllers
          initialBank
            (profiledRawJointHybridMegaLinkedFrontTwoOfReplacementOwner A
              strategy hwin controllers initialBank owner)) inputTwo
        (profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin controllers
          initialBank
            (profiledRawJointHybridMegaLinkedFrontOneOfShadow A strategy hwin
              controllers initialBank shadow)) inputOne =
      (default,
        profiledRawJointHybridMegaLinkedTailInitialTwo A strategy hwin
          controllers initialBank
            (profiledRawJointHybridShadowPhaseLiveLeftTag A strategy hwin
              shadow.origin shadow.input)) :=
  rfl

@[simp] theorem
    profiledRawJointHybridMegaLinkedUnconditionalExceptionalAdapter_left_entry
    (fallbackTag : RetainedTag A strategy hwin)
    (shadow : OneShadow A strategy hwin)
    (owner : LeftGuardOwner A strategy hwin)
    (inputOne : In₁) (inputTwo : In₂) :
    (profiledRawJointHybridMegaLinkedUnconditionalExceptionalAdapter A strategy
      hwin controllers initialBank fallbackTag).otherRecvOne
        (profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin controllers
          initialBank
          (profiledRawJointHybridMegaLinkedFrontOneOfShadow A strategy hwin
            controllers initialBank shadow)) inputOne
        (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin controllers
          initialBank
          (profiledRawJointHybridMegaLinkedFrontTwoOfLeftGuardOwner A strategy
            hwin controllers initialBank owner)) inputTwo =
      profiledRawJointHybridMegaLinkedEnterTailOne A strategy hwin controllers
        initialBank shadow owner inputOne inputTwo :=
  rfl

@[simp] theorem
    profiledRawJointHybridMegaLinkedUnconditionalExceptionalAdapter_right_entry
    (fallbackTag : RetainedTag A strategy hwin)
    (shadow : TwoShadow A strategy hwin)
    (owner : RightGuardOwner A strategy hwin)
    (inputTwo : In₂) (inputOne : In₁) :
    (profiledRawJointHybridMegaLinkedUnconditionalExceptionalAdapter A strategy
      hwin controllers initialBank fallbackTag).otherRecvTwo
        (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin controllers
          initialBank
          (profiledRawJointHybridMegaLinkedFrontTwoOfShadow A strategy hwin
            controllers initialBank shadow)) inputTwo
        (profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin controllers
          initialBank
          (profiledRawJointHybridMegaLinkedFrontOneOfRightGuardOwner A strategy
            hwin controllers initialBank owner)) inputOne =
      profiledRawJointHybridMegaLinkedEnterTailTwo A strategy hwin controllers
        initialBank shadow owner inputTwo inputOne :=
  rfl

@[simp] theorem
    profiledRawJointHybridMegaLinkedUnconditionalExceptionalAdapter_right_owner_entry
    (fallbackTag : RetainedTag A strategy hwin)
    (owner : RightGuardOwner A strategy hwin)
    (shadow : TwoShadow A strategy hwin)
    (inputOne : In₁) (inputTwo : In₂) :
    (profiledRawJointHybridMegaLinkedUnconditionalExceptionalAdapter A strategy
      hwin controllers initialBank fallbackTag).otherRecvOne
        (profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin controllers
          initialBank
          (profiledRawJointHybridMegaLinkedFrontOneOfRightGuardOwner A strategy
            hwin controllers initialBank owner)) inputOne
        (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin controllers
          initialBank
          (profiledRawJointHybridMegaLinkedFrontTwoOfShadow A strategy hwin
            controllers initialBank shadow)) inputTwo =
      profiledRawJointHybridMegaLinkedEnterTailOneFromRightGuardOwner A strategy
        hwin controllers initialBank owner shadow inputOne inputTwo :=
  rfl

@[simp] theorem
    profiledRawJointHybridMegaLinkedUnconditionalExceptionalAdapter_left_owner_entry
    (fallbackTag : RetainedTag A strategy hwin)
    (owner : LeftGuardOwner A strategy hwin)
    (shadow : OneShadow A strategy hwin)
    (inputTwo : In₂) (inputOne : In₁) :
    (profiledRawJointHybridMegaLinkedUnconditionalExceptionalAdapter A strategy
      hwin controllers initialBank fallbackTag).otherRecvTwo
        (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin controllers
          initialBank
          (profiledRawJointHybridMegaLinkedFrontTwoOfLeftGuardOwner A strategy
            hwin controllers initialBank owner)) inputTwo
        (profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin controllers
          initialBank
          (profiledRawJointHybridMegaLinkedFrontOneOfShadow A strategy hwin
            controllers initialBank shadow)) inputOne =
      profiledRawJointHybridMegaLinkedEnterTailTwoFromLeftGuardOwner A strategy
        hwin controllers initialBank owner shadow inputTwo inputOne :=
  rfl

@[simp] theorem profiledRawJointHybridMegaLinkedEnterTailOne_retainedTag
    (shadow : OneShadow A strategy hwin)
    (owner : LeftGuardOwner A strategy hwin)
    (inputOne : In₁) (inputTwo : In₂) :
    match
        (profiledRawJointHybridMegaLinkedEnterTailOne A strategy hwin
          controllers initialBank shadow owner inputOne inputTwo).2 with
    | .exceptional (.inr tail) =>
        tail.1 =
          (profiledRawJointHybridOneShadowRecvLeftOwnerPhaseLive A strategy
            hwin shadow owner inputOne inputTwo).2.tag.markedRetainedChildTag A
              strategy hwin
    | _ => False :=
  rfl

@[simp] theorem profiledRawJointHybridMegaLinkedEnterTailTwo_retainedTag
    (shadow : TwoShadow A strategy hwin)
    (owner : RightGuardOwner A strategy hwin)
    (inputTwo : In₂) (inputOne : In₁) :
    match
        (profiledRawJointHybridMegaLinkedEnterTailTwo A strategy hwin
          controllers initialBank shadow owner inputTwo inputOne).2 with
    | .exceptional (.inr tail) =>
        tail.1 =
          (profiledRawJointHybridTwoShadowRecvRightOwnerPhaseLive A strategy
            hwin shadow owner inputTwo inputOne).2.tag.markedRetainedChildTag A
              strategy hwin
    | _ => False :=
  rfl

@[simp] theorem
    profiledRawJointHybridMegaLinkedEnterTailOneFromRightGuardOwner_retainedTag
    (owner : RightGuardOwner A strategy hwin)
    (shadow : TwoShadow A strategy hwin)
    (inputOne : In₁) (inputTwo : In₂) :
    match
        (profiledRawJointHybridMegaLinkedEnterTailOneFromRightGuardOwner A
          strategy hwin controllers initialBank owner shadow inputOne
            inputTwo).2 with
    | .exceptional (.inr tail) =>
        tail.1 =
          (profiledRawJointHybridTwoShadowRecvRightOwnerPhaseLive A strategy
            hwin shadow owner inputTwo inputOne).2.tag.markedRetainedChildTag A
              strategy hwin
    | _ => False :=
  rfl

@[simp] theorem
    profiledRawJointHybridMegaLinkedEnterTailTwoFromLeftGuardOwner_retainedTag
    (owner : LeftGuardOwner A strategy hwin)
    (shadow : OneShadow A strategy hwin)
    (inputTwo : In₂) (inputOne : In₁) :
    match
        (profiledRawJointHybridMegaLinkedEnterTailTwoFromLeftGuardOwner A
          strategy hwin controllers initialBank owner shadow inputTwo
            inputOne).2 with
    | .exceptional (.inr tail) =>
        tail.1 =
          (profiledRawJointHybridOneShadowRecvLeftOwnerPhaseLive A strategy
            hwin shadow owner inputOne inputTwo).2.tag.markedRetainedChildTag A
              strategy hwin
    | _ => False :=
  rfl

/-- Both endpoints of a strict-right simultaneous handoff install literally
the same retained child.  No endpoint tests which side is currently informed;
the equality follows from the shared delivered shadow. -/
@[simp] theorem
    profiledRawJointHybridMegaLinkedRightEntry_shared_retainedTag
    (owner : RightGuardOwner A strategy hwin)
    (shadow : TwoShadow A strategy hwin)
    (inputOne : In₁) (inputTwo : In₂) :
    match
        (profiledRawJointHybridMegaLinkedEnterTailOneFromRightGuardOwner A
          strategy hwin controllers initialBank owner shadow inputOne
            inputTwo).2,
        (profiledRawJointHybridMegaLinkedEnterTailTwo A strategy hwin
          controllers initialBank shadow owner inputTwo inputOne).2 with
    | .exceptional (.inr one), .exceptional (.inr two) => one.1 = two.1
    | _, _ => False :=
  rfl

/-- Strict-left mirror of shared-child installation. -/
@[simp] theorem
    profiledRawJointHybridMegaLinkedLeftEntry_shared_retainedTag
    (shadow : OneShadow A strategy hwin)
    (owner : LeftGuardOwner A strategy hwin)
    (inputOne : In₁) (inputTwo : In₂) :
    match
        (profiledRawJointHybridMegaLinkedEnterTailOne A strategy hwin
          controllers initialBank shadow owner inputOne inputTwo).2,
        (profiledRawJointHybridMegaLinkedEnterTailTwoFromLeftGuardOwner A
          strategy hwin controllers initialBank owner shadow inputTwo
            inputOne).2 with
    | .exceptional (.inr one), .exceptional (.inr two) => one.1 = two.1
    | _, _ => False :=
  rfl

@[simp] theorem
    profiledRawJointHybridMegaLinkedExceptionalAdapter_noRecvOne_tail
    (fallbackTag : RetainedTag A strategy hwin)
    (maps : ProfiledRawJointHybridMegaLinkedFrontReceiveMaps A strategy hwin
      controllers initialBank)
    (tail : TailOne A strategy hwin) (input : In₁) :
    (profiledRawJointHybridMegaLinkedExceptionalAdapter A strategy hwin
      controllers initialBank fallbackTag maps).exceptionalNoRecvOne
        (.inr tail) input =
      profiledRawJointHybridMegaLinkedExceptionalNoRecvOne A strategy hwin
        controllers initialBank (.inr tail) input :=
  rfl

@[simp] theorem
    profiledRawJointHybridMegaLinkedExceptionalAdapter_noRecvTwo_tail
    (fallbackTag : RetainedTag A strategy hwin)
    (maps : ProfiledRawJointHybridMegaLinkedFrontReceiveMaps A strategy hwin
      controllers initialBank)
    (tail : TailTwo A strategy hwin) (input : In₂) :
    (profiledRawJointHybridMegaLinkedExceptionalAdapter A strategy hwin
      controllers initialBank fallbackTag maps).exceptionalNoRecvTwo
        (.inr tail) input =
      profiledRawJointHybridMegaLinkedExceptionalNoRecvTwo A strategy hwin
        controllers initialBank (.inr tail) input :=
  rfl

@[simp] theorem
    profiledRawJointHybridMegaLinkedExceptionalAdapter_frontTailOne
    (fallbackTag : RetainedTag A strategy hwin)
    (maps : ProfiledRawJointHybridMegaLinkedFrontReceiveMaps A strategy hwin
      controllers initialBank)
    (front : OldOne A strategy hwin controllers initialBank)
    (inputOne : In₁) (tail : TailTwo A strategy hwin) (inputTwo : In₂) :
    (profiledRawJointHybridMegaLinkedExceptionalAdapter A strategy hwin
      controllers initialBank fallbackTag maps).otherRecvOne
        (profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin controllers
          initialBank front) inputOne
        (profiledRawJointHybridMegaLinkedInjectTailTwo A strategy hwin
          controllers initialBank tail) inputTwo =
      profiledRawJointHybridMegaLinkedFrontTailRecvOne A strategy hwin
        controllers initialBank front inputOne tail inputTwo := by
  cases front <;> rfl

@[simp] theorem
    profiledRawJointHybridMegaLinkedExceptionalAdapter_frontTailTwo
    (fallbackTag : RetainedTag A strategy hwin)
    (maps : ProfiledRawJointHybridMegaLinkedFrontReceiveMaps A strategy hwin
      controllers initialBank)
    (front : OldTwo A strategy hwin controllers initialBank)
    (inputTwo : In₂) (tail : TailOne A strategy hwin) (inputOne : In₁) :
    (profiledRawJointHybridMegaLinkedExceptionalAdapter A strategy hwin
      controllers initialBank fallbackTag maps).otherRecvTwo
        (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin controllers
          initialBank front) inputTwo
        (profiledRawJointHybridMegaLinkedInjectTailOne A strategy hwin
          controllers initialBank tail) inputOne =
      profiledRawJointHybridMegaLinkedFrontTailRecvTwo A strategy hwin
        controllers initialBank front inputTwo tail inputOne := by
  cases front <;> rfl

@[simp] theorem
    profiledRawJointHybridMegaLinkedExceptionalAdapter_tailFrontOne
    (fallbackTag : RetainedTag A strategy hwin)
    (maps : ProfiledRawJointHybridMegaLinkedFrontReceiveMaps A strategy hwin
      controllers initialBank)
    (tail : TailOne A strategy hwin) (inputOne : In₁)
    (front : OldTwo A strategy hwin controllers initialBank)
    (inputTwo : In₂) :
    (profiledRawJointHybridMegaLinkedExceptionalAdapter A strategy hwin
      controllers initialBank fallbackTag maps).otherRecvOne
        (profiledRawJointHybridMegaLinkedInjectTailOne A strategy hwin
          controllers initialBank tail) inputOne
        (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin controllers
          initialBank front) inputTwo =
      profiledRawJointHybridMegaLinkedTailFrontRecvOne A strategy hwin
        controllers initialBank tail inputOne front inputTwo := by
  cases front <;> rfl

@[simp] theorem
    profiledRawJointHybridMegaLinkedExceptionalAdapter_tailFrontTwo
    (fallbackTag : RetainedTag A strategy hwin)
    (maps : ProfiledRawJointHybridMegaLinkedFrontReceiveMaps A strategy hwin
      controllers initialBank)
    (tail : TailTwo A strategy hwin) (inputTwo : In₂)
    (front : OldOne A strategy hwin controllers initialBank)
    (inputOne : In₁) :
    (profiledRawJointHybridMegaLinkedExceptionalAdapter A strategy hwin
      controllers initialBank fallbackTag maps).otherRecvTwo
        (profiledRawJointHybridMegaLinkedInjectTailTwo A strategy hwin
          controllers initialBank tail) inputTwo
        (profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin controllers
          initialBank front) inputOne =
      profiledRawJointHybridMegaLinkedTailFrontRecvTwo A strategy hwin
        controllers initialBank tail inputTwo front inputOne := by
  cases front <;> rfl

/-- The actual global leader-free kernel.  Although the compatibility input is
a six-field record, the exact override makes the kernel depend externally only
on the two front/front totalization rows. -/
noncomputable def profiledRawJointHybridMegaLinkedLeaderFreeKernel
    (fallbackTag : RetainedTag A strategy hwin)
    (maps : ProfiledRawJointHybridMegaLinkedFrontReceiveMaps A strategy hwin
      controllers initialBank) :=
  profiledRawJointHybridMegaLeaderFreeKernel A strategy hwin initialBank
    (profiledRawJointHybridMegaLinkedExceptionalAdapter A strategy hwin
      controllers initialBank fallbackTag maps)

/-- Minimal two-row form of the global leader-free kernel. -/
noncomputable def
    profiledRawJointHybridMegaLinkedLeaderFreeKernelOfFrontFront
    (fallbackTag : RetainedTag A strategy hwin)
    (maps : ProfiledRawJointHybridMegaLinkedFrontFrontReceiveMaps A strategy
      hwin controllers initialBank) :=
  profiledRawJointHybridMegaLinkedLeaderFreeKernel A strategy hwin controllers
    initialBank fallbackTag
      (profiledRawJointHybridMegaLinkedFrontReceiveMapsOfFrontFront A strategy
        hwin controllers initialBank maps)

/-- Closed leader-free kernel with no external receive-map datum.  The default
front/front rows merely make the finite transition function total; root and
genuine handoff rows are intercepted by the canonical equations above. -/
noncomputable def
    profiledRawJointHybridMegaLinkedUnconditionalLeaderFreeKernel
    (fallbackTag : RetainedTag A strategy hwin) :=
  profiledRawJointHybridMegaLeaderFreeKernel A strategy hwin initialBank
    (profiledRawJointHybridMegaLinkedUnconditionalExceptionalAdapter A strategy
      hwin controllers initialBank fallbackTag)

/-- The legacy fallback-tag argument is not inspected by any transition of
the closed mega front.  Runtime tail states carry their own installed tag, so
changing this proof-side totalization parameter changes no controller data. -/
theorem
    profiledRawJointHybridMegaLinkedUnconditionalLeaderFreeKernel_tag_irrel
    (left right : RetainedTag A strategy hwin) :
    profiledRawJointHybridMegaLinkedUnconditionalLeaderFreeKernel A strategy
        hwin controllers initialBank left =
      profiledRawJointHybridMegaLinkedUnconditionalLeaderFreeKernel A strategy
        hwin controllers initialBank right :=
  rfl

/-! ## Physical tail embedding

The preceding four equations lift to the whole physical round transition.
This is the splice fact needed later: after a pair has entered the linked
tail, the mega controller is a conservative extension of that tail on every
future graph letter. -/

private abbrev LinkedTailPhysicalController
    (fallbackTag : RetainedTag A strategy hwin) :=
  profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartController
    A strategy hwin fallbackTag

private abbrev MegaLinkedKernel
    (fallbackTag : RetainedTag A strategy hwin)
    (maps : ProfiledRawJointHybridMegaLinkedFrontReceiveMaps A strategy hwin
      controllers initialBank) :=
  profiledRawJointHybridMegaLinkedLeaderFreeKernel A strategy hwin controllers
    initialBank fallbackTag maps

private abbrev MegaLinkedPhysicalController
    (fallbackTag : RetainedTag A strategy hwin)
    (maps : ProfiledRawJointHybridMegaLinkedFrontReceiveMaps A strategy hwin
      controllers initialBank) :=
  (MegaLinkedKernel A strategy hwin controllers initialBank fallbackTag maps
    ).physicalController

private noncomputable abbrev MegaLinkedClosedMaps :=
  profiledRawJointHybridMegaLinkedFrontReceiveMapsOfFrontFront A strategy hwin
    controllers initialBank
      (profiledRawJointHybridMegaLinkedDefaultFrontFrontReceiveMaps A strategy
        hwin controllers initialBank)

abbrev MegaLinkedUnconditionalPhysicalController
    (fallbackTag : RetainedTag A strategy hwin) :=
  (profiledRawJointHybridMegaLinkedUnconditionalLeaderFreeKernel A strategy
    hwin controllers initialBank fallbackTag).physicalController

theorem
    profiledRawJointHybridMegaLinkedUnconditionalPhysicalController_tag_irrel
    (left right : RetainedTag A strategy hwin) :
    MegaLinkedUnconditionalPhysicalController A strategy hwin controllers
        initialBank left =
      MegaLinkedUnconditionalPhysicalController A strategy hwin controllers
        initialBank right :=
  congrArg (fun kernel => kernel.physicalController)
    (profiledRawJointHybridMegaLinkedUnconditionalLeaderFreeKernel_tag_irrel A
      strategy hwin controllers initialBank left right)

/-! ## Physical states at a genuine simultaneous entry -/

noncomputable def profiledRawJointHybridMegaLinkedRightEntryRetainedTag
    (shadow : TwoShadow A strategy hwin)
    (owner : RightGuardOwner A strategy hwin)
    (inputOne : In₁) (inputTwo : In₂) : RetainedTag A strategy hwin :=
  (profiledRawJointHybridTwoShadowRecvRightOwnerPhaseLive A strategy hwin
    shadow owner inputTwo inputOne).2.tag.markedRetainedChildTag A strategy hwin

noncomputable def profiledRawJointHybridMegaLinkedLeftEntryRetainedTag
    (shadow : OneShadow A strategy hwin)
    (owner : LeftGuardOwner A strategy hwin)
    (inputOne : In₁) (inputTwo : In₂) : RetainedTag A strategy hwin :=
  (profiledRawJointHybridOneShadowRecvLeftOwnerPhaseLive A strategy hwin
    shadow owner inputOne inputTwo).2.tag.markedRetainedChildTag A strategy hwin

/-- The old mega-linked handoff tag is the child selected by the *first*
strict-right letter stored in the shadow.  It does not retain the checked
target emitted by the later simultaneous close. -/
@[simp] theorem profiledRawJointHybridMegaLinkedRightEntryRetainedTag_state
    (shadow : TwoShadow A strategy hwin)
    (owner : RightGuardOwner A strategy hwin)
    (inputOne : In₁) (inputTwo : In₂) :
    (profiledRawJointHybridMegaLinkedRightEntryRetainedTag A strategy hwin
      shadow owner inputOne inputTwo).1 =
      (profiledRawJointHybridShadowPhaseLiveRightTag A strategy hwin
        shadow.origin shadow.input).markedBankChild A strategy hwin := by
  rfl

/-- Strict-left mirror: this is the first strict child, not a reified target
of the later close record. -/
@[simp] theorem profiledRawJointHybridMegaLinkedLeftEntryRetainedTag_state
    (shadow : OneShadow A strategy hwin)
    (owner : LeftGuardOwner A strategy hwin)
    (inputOne : In₁) (inputTwo : In₂) :
    (profiledRawJointHybridMegaLinkedLeftEntryRetainedTag A strategy hwin
      shadow owner inputOne inputTwo).1 =
      (profiledRawJointHybridShadowPhaseLiveLeftTag A strategy hwin
        shadow.origin shadow.input).markedBankChild A strategy hwin := by
  rfl

/-- The linked physical state immediately after the strict-right `.both`
handoff.  Its underlying controls are the canonical roots; its Moore outputs
are exactly the two outputs emitted by the front handoff round. -/
noncomputable def profiledRawJointHybridMegaLinkedRightEntryTailPhysicalPair
    (shadow : TwoShadow A strategy hwin)
    (owner : RightGuardOwner A strategy hwin)
    (inputOne : In₁) (inputTwo : In₂) :
    let tag := profiledRawJointHybridMegaLinkedRightEntryRetainedTag A strategy
      hwin shadow owner inputOne inputTwo
    (LinkedTailPhysicalController A strategy hwin tag).OneControl ×
      (LinkedTailPhysicalController A strategy hwin tag).TwoControl :=
  let tag := profiledRawJointHybridMegaLinkedRightEntryRetainedTag A strategy
    hwin shadow owner inputOne inputTwo
  let fork :=
    profiledRawJointHybridMegaLinkedTailCommonRootForkPair A strategy hwin tag
  ((fork.1,
      (profiledRawJointHybridMegaLinkedEnterTailOneFromRightGuardOwner A
        strategy hwin controllers initialBank owner shadow inputOne
          inputTwo).1),
    (fork.2,
      (profiledRawJointHybridMegaLinkedEnterTailTwo A strategy hwin controllers
        initialBank shadow owner inputTwo inputOne).1))

/-- Strict-left mirror. -/
noncomputable def profiledRawJointHybridMegaLinkedLeftEntryTailPhysicalPair
    (shadow : OneShadow A strategy hwin)
    (owner : LeftGuardOwner A strategy hwin)
    (inputOne : In₁) (inputTwo : In₂) :
    let tag := profiledRawJointHybridMegaLinkedLeftEntryRetainedTag A strategy
      hwin shadow owner inputOne inputTwo
    (LinkedTailPhysicalController A strategy hwin tag).OneControl ×
      (LinkedTailPhysicalController A strategy hwin tag).TwoControl :=
  let tag := profiledRawJointHybridMegaLinkedLeftEntryRetainedTag A strategy
    hwin shadow owner inputOne inputTwo
  let fork :=
    profiledRawJointHybridMegaLinkedTailCommonRootForkPair A strategy hwin tag
  ((fork.1,
      (profiledRawJointHybridMegaLinkedEnterTailOne A strategy hwin controllers
        initialBank shadow owner inputOne inputTwo).1),
    (fork.2,
      (profiledRawJointHybridMegaLinkedEnterTailTwoFromLeftGuardOwner A strategy
        hwin controllers initialBank owner shadow inputTwo inputOne).1))

@[simp] theorem profiledRawJointHybridMegaLinkedKernel_noRecvOne_tail
    (fallbackTag : RetainedTag A strategy hwin)
    (maps : ProfiledRawJointHybridMegaLinkedFrontReceiveMaps A strategy hwin
      controllers initialBank)
    (tail : TailOne A strategy hwin) (input : In₁) :
    (MegaLinkedKernel A strategy hwin controllers initialBank fallbackTag maps
      ).noRecvOne
        (profiledRawJointHybridMegaLinkedInjectTailOne A strategy hwin
          controllers initialBank tail) input =
      profiledRawJointHybridMegaLinkedExceptionalNoRecvOne A strategy hwin
        controllers initialBank (.inr tail) input :=
  rfl

@[simp] theorem profiledRawJointHybridMegaLinkedKernel_noRecvTwo_tail
    (fallbackTag : RetainedTag A strategy hwin)
    (maps : ProfiledRawJointHybridMegaLinkedFrontReceiveMaps A strategy hwin
      controllers initialBank)
    (tail : TailTwo A strategy hwin) (input : In₂) :
    (MegaLinkedKernel A strategy hwin controllers initialBank fallbackTag maps
      ).noRecvTwo
        (profiledRawJointHybridMegaLinkedInjectTailTwo A strategy hwin
          controllers initialBank tail) input =
      profiledRawJointHybridMegaLinkedExceptionalNoRecvTwo A strategy hwin
        controllers initialBank (.inr tail) input :=
  rfl

@[simp] theorem profiledRawJointHybridMegaLinkedKernel_frontTailOne
    (fallbackTag : RetainedTag A strategy hwin)
    (maps : ProfiledRawJointHybridMegaLinkedFrontReceiveMaps A strategy hwin
      controllers initialBank)
    (front : OldOne A strategy hwin controllers initialBank)
    (inputOne : In₁) (tail : TailTwo A strategy hwin) (inputTwo : In₂) :
    (MegaLinkedKernel A strategy hwin controllers initialBank fallbackTag maps
      ).recvOne
        (profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin controllers
          initialBank front) inputOne
        (profiledRawJointHybridMegaLinkedInjectTailTwo A strategy hwin
          controllers initialBank tail) inputTwo =
      profiledRawJointHybridMegaLinkedFrontTailRecvOne A strategy hwin
        controllers initialBank front inputOne tail inputTwo := by
  cases front <;> rfl

@[simp] theorem profiledRawJointHybridMegaLinkedKernel_frontTailTwo
    (fallbackTag : RetainedTag A strategy hwin)
    (maps : ProfiledRawJointHybridMegaLinkedFrontReceiveMaps A strategy hwin
      controllers initialBank)
    (front : OldTwo A strategy hwin controllers initialBank)
    (inputTwo : In₂) (tail : TailOne A strategy hwin) (inputOne : In₁) :
    (MegaLinkedKernel A strategy hwin controllers initialBank fallbackTag maps
      ).recvTwo
        (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin controllers
          initialBank front) inputTwo
        (profiledRawJointHybridMegaLinkedInjectTailOne A strategy hwin
          controllers initialBank tail) inputOne =
      profiledRawJointHybridMegaLinkedFrontTailRecvTwo A strategy hwin
        controllers initialBank front inputTwo tail inputOne := by
  cases front <;> rfl

@[simp] theorem profiledRawJointHybridMegaLinkedKernel_tailFrontOne
    (fallbackTag : RetainedTag A strategy hwin)
    (maps : ProfiledRawJointHybridMegaLinkedFrontReceiveMaps A strategy hwin
      controllers initialBank)
    (tail : TailOne A strategy hwin) (inputOne : In₁)
    (front : OldTwo A strategy hwin controllers initialBank)
    (inputTwo : In₂) :
    (MegaLinkedKernel A strategy hwin controllers initialBank fallbackTag maps
      ).recvOne
        (profiledRawJointHybridMegaLinkedInjectTailOne A strategy hwin
          controllers initialBank tail) inputOne
        (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin controllers
          initialBank front) inputTwo =
      profiledRawJointHybridMegaLinkedTailFrontRecvOne A strategy hwin
        controllers initialBank tail inputOne front inputTwo := by
  cases front <;> rfl

@[simp] theorem profiledRawJointHybridMegaLinkedKernel_tailFrontTwo
    (fallbackTag : RetainedTag A strategy hwin)
    (maps : ProfiledRawJointHybridMegaLinkedFrontReceiveMaps A strategy hwin
      controllers initialBank)
    (tail : TailTwo A strategy hwin) (inputTwo : In₂)
    (front : OldOne A strategy hwin controllers initialBank)
    (inputOne : In₁) :
    (MegaLinkedKernel A strategy hwin controllers initialBank fallbackTag maps
      ).recvTwo
        (profiledRawJointHybridMegaLinkedInjectTailTwo A strategy hwin
          controllers initialBank tail) inputTwo
        (profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin controllers
          initialBank front) inputOne =
      profiledRawJointHybridMegaLinkedTailFrontRecvTwo A strategy hwin
        controllers initialBank tail inputTwo front inputOne := by
  cases front <;> rfl

/-- Embed one physical process-one tail state in the exceptional summand of
the mega controller, preserving its last emitted output. -/
noncomputable def profiledRawJointHybridMegaLinkedEmbedTailPhysicalOne
    (fallbackTag : RetainedTag A strategy hwin)
    (maps : ProfiledRawJointHybridMegaLinkedFrontReceiveMaps A strategy hwin
      controllers initialBank)
    (state :
      (LinkedTailPhysicalController A strategy hwin fallbackTag).OneControl) :
    (MegaLinkedPhysicalController A strategy hwin controllers initialBank
      fallbackTag maps).OneControl :=
  (profiledRawJointHybridMegaLinkedInjectTailOne A strategy hwin controllers
    initialBank (fallbackTag, state.1), state.2)

/-- Process-two mirror. -/
noncomputable def profiledRawJointHybridMegaLinkedEmbedTailPhysicalTwo
    (fallbackTag : RetainedTag A strategy hwin)
    (maps : ProfiledRawJointHybridMegaLinkedFrontReceiveMaps A strategy hwin
      controllers initialBank)
    (state :
      (LinkedTailPhysicalController A strategy hwin fallbackTag).TwoControl) :
    (MegaLinkedPhysicalController A strategy hwin controllers initialBank
      fallbackTag maps).TwoControl :=
  (profiledRawJointHybridMegaLinkedInjectTailTwo A strategy hwin controllers
    initialBank (fallbackTag, state.1), state.2)

/-- Pairwise physical embedding used by the suffix trace theorem. -/
noncomputable def profiledRawJointHybridMegaLinkedEmbedTailPhysicalPair
    (fallbackTag : RetainedTag A strategy hwin)
    (maps : ProfiledRawJointHybridMegaLinkedFrontReceiveMaps A strategy hwin
      controllers initialBank)
    (state :
      (LinkedTailPhysicalController A strategy hwin fallbackTag).OneControl ×
        (LinkedTailPhysicalController A strategy hwin fallbackTag).TwoControl) :
    (MegaLinkedPhysicalController A strategy hwin controllers initialBank
      fallbackTag maps).OneControl ×
      (MegaLinkedPhysicalController A strategy hwin controllers initialBank
        fallbackTag maps).TwoControl :=
  (profiledRawJointHybridMegaLinkedEmbedTailPhysicalOne A strategy hwin
      controllers initialBank fallbackTag maps state.1,
    profiledRawJointHybridMegaLinkedEmbedTailPhysicalTwo A strategy hwin
      controllers initialBank fallbackTag maps state.2)

/-! ## Reachable simultaneous front rows -/

/- A simultaneous root enters the honest pair of initial ambiguity shadows. -/
set_option maxHeartbeats 1000000 in
theorem profiledRawJointHybridMegaLinkedUnconditional_root_both
    (kernelTag : RetainedTag A strategy hwin)
    (inputOne : In₁) (inputTwo : In₂) :
    let mega := MegaLinkedUnconditionalPhysicalController A strategy hwin
      controllers initialBank kernelTag
    let nextOne := profiledRawJointHybridInitialRootRecvOne A strategy hwin
      controllers (inputOne, inputTwo)
    let nextTwo := profiledRawJointHybridInitialRootRecvTwo A strategy hwin
      controllers (inputOne, inputTwo)
    mega.advanceControls (mega.initialOne, mega.initialTwo)
        ⟨inputOne, inputTwo, .both⟩ =
      ((profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin controllers
          initialBank (.exceptional
            (profiledRawJointHybridMegaExceptionalOneOfInitialShadow A strategy
              hwin controllers initialBank nextOne.2)), nextOne.1),
        (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin controllers
          initialBank (.exceptional
            (profiledRawJointHybridMegaExceptionalTwoOfInitialShadow A strategy
              hwin controllers initialBank nextTwo.2)), nextTwo.1)) := by
  rfl

/- A second simultaneous round retains the exact strict contingency and enters
the coupled pre-rationalized sibling startup pair. -/
set_option maxHeartbeats 1000000 in
theorem profiledRawJointHybridMegaLinkedUnconditional_initialShadows_both
    (kernelTag : RetainedTag A strategy hwin)
    (shadowOne : ProfiledRawJointHybridInitialOneShadow A strategy hwin
      controllers)
    (shadowTwo : ProfiledRawJointHybridInitialTwoShadow A strategy hwin
      controllers)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (inputOne : In₁) (inputTwo : In₂) :
    let mega := MegaLinkedUnconditionalPhysicalController A strategy hwin
      controllers initialBank kernelTag
    let nextOne := profiledRawJointHybridMegaInitialToCoupledOne A strategy hwin
      controllers shadowTwo inputOne inputTwo
    let nextTwo := profiledRawJointHybridMegaInitialToCoupledTwo A strategy hwin
      controllers shadowOne inputTwo inputOne
    mega.advanceControls
        ((profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin controllers
            initialBank (.exceptional
              (profiledRawJointHybridMegaExceptionalOneOfInitialShadow A
                strategy hwin controllers initialBank shadowOne)),
            oldOutputOne),
          (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin
            controllers initialBank (.exceptional
              (profiledRawJointHybridMegaExceptionalTwoOfInitialShadow A
                strategy hwin controllers initialBank shadowTwo)),
            oldOutputTwo))
        ⟨inputOne, inputTwo, .both⟩ =
      ((profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin controllers
          initialBank (.exceptional
            (profiledRawJointHybridMegaExceptionalOneOfPinnedInitial A strategy
              hwin controllers initialBank
                (.inr (.inl nextOne.2)))), nextOne.1),
        (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin controllers
          initialBank (.exceptional
            (profiledRawJointHybridMegaExceptionalTwoOfPinnedInitial A strategy
              hwin controllers initialBank
                (.inr (.inl nextTwo.2)))), nextTwo.1)) := by
  rfl

/- Once both endpoints carry generic shadows, every simultaneous round
refreshes that pair without falling through to a default front row. -/
set_option maxHeartbeats 1000000 in
theorem profiledRawJointHybridMegaLinkedUnconditional_shadows_both
    (kernelTag : RetainedTag A strategy hwin)
    (shadowOne : OneShadow A strategy hwin)
    (shadowTwo : TwoShadow A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (inputOne : In₁) (inputTwo : In₂) :
    let mega := MegaLinkedUnconditionalPhysicalController A strategy hwin
      controllers initialBank kernelTag
    let nextOne := profiledRawJointHybridOneShadowRecvCommon A strategy hwin
      shadowOne shadowTwo inputOne inputTwo
    let nextTwo := profiledRawJointHybridTwoShadowRecvCommon A strategy hwin
      shadowTwo shadowOne inputTwo inputOne
    mega.advanceControls
        ((profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin controllers
            initialBank
              (profiledRawJointHybridMegaLinkedFrontOneOfShadow A strategy hwin
                controllers initialBank shadowOne), oldOutputOne),
          (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin
            controllers initialBank
              (profiledRawJointHybridMegaLinkedFrontTwoOfShadow A strategy hwin
                controllers initialBank shadowTwo), oldOutputTwo))
        ⟨inputOne, inputTwo, .both⟩ =
      ((profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin controllers
          initialBank
            (profiledRawJointHybridMegaLinkedFrontOneOfShadow A strategy hwin
              controllers initialBank nextOne.2), nextOne.1),
        (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin controllers
          initialBank
            (profiledRawJointHybridMegaLinkedFrontTwoOfShadow A strategy hwin
              controllers initialBank nextTwo.2), nextTwo.1)) := by
  rfl

/- A strict-right round from the common-shadow pair creates exactly the
indexed replacement owner and the refreshed informed shadow consumed by the
next resolving row. -/
set_option maxHeartbeats 1000000 in
theorem profiledRawJointHybridMegaLinkedUnconditional_shadows_right
    (kernelTag : RetainedTag A strategy hwin)
    (shadowOne : OneShadow A strategy hwin)
    (shadowTwo : TwoShadow A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (inputOne : In₁) (inputTwo : In₂) :
    let mega := MegaLinkedUnconditionalPhysicalController A strategy hwin
      controllers initialBank kernelTag
    let nextOne := profiledRawJointHybridOneShadowNoRecv A strategy hwin
      shadowOne inputOne
    let nextTwo := profiledRawJointHybridTwoShadowRecvCommon A strategy hwin
      shadowTwo shadowOne inputTwo inputOne
    mega.advanceControls
        ((profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin controllers
            initialBank
              (profiledRawJointHybridMegaLinkedFrontOneOfShadow A strategy hwin
                controllers initialBank shadowOne), oldOutputOne),
          (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin
            controllers initialBank
              (profiledRawJointHybridMegaLinkedFrontTwoOfShadow A strategy hwin
                controllers initialBank shadowTwo), oldOutputTwo))
        ⟨inputOne, inputTwo, .right⟩ =
      ((profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin controllers
          initialBank
            (profiledRawJointHybridMegaLinkedFrontOneOfReplacementOwner A
              strategy hwin controllers initialBank nextOne.2), nextOne.1),
        (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin controllers
          initialBank
            (profiledRawJointHybridMegaLinkedFrontTwoOfShadow A strategy hwin
              controllers initialBank nextTwo.2), nextTwo.1)) := by
  rfl

/- Strict-left mirror. -/
set_option maxHeartbeats 1000000 in
theorem profiledRawJointHybridMegaLinkedUnconditional_shadows_left
    (kernelTag : RetainedTag A strategy hwin)
    (shadowOne : OneShadow A strategy hwin)
    (shadowTwo : TwoShadow A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (inputOne : In₁) (inputTwo : In₂) :
    let mega := MegaLinkedUnconditionalPhysicalController A strategy hwin
      controllers initialBank kernelTag
    let nextOne := profiledRawJointHybridOneShadowRecvCommon A strategy hwin
      shadowOne shadowTwo inputOne inputTwo
    let nextTwo := profiledRawJointHybridTwoShadowNoRecv A strategy hwin
      shadowTwo inputTwo
    mega.advanceControls
        ((profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin controllers
            initialBank
              (profiledRawJointHybridMegaLinkedFrontOneOfShadow A strategy hwin
                controllers initialBank shadowOne), oldOutputOne),
          (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin
            controllers initialBank
              (profiledRawJointHybridMegaLinkedFrontTwoOfShadow A strategy hwin
                controllers initialBank shadowTwo), oldOutputTwo))
        ⟨inputOne, inputTwo, .left⟩ =
      ((profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin controllers
          initialBank
            (profiledRawJointHybridMegaLinkedFrontOneOfShadow A strategy hwin
              controllers initialBank nextOne.2), nextOne.1),
        (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin controllers
          initialBank
            (profiledRawJointHybridMegaLinkedFrontTwoOfReplacementOwner A
              strategy hwin controllers initialBank nextTwo.2), nextTwo.1)) := by
  rfl

/- A replacement owner meeting the informed shadow closes directly into the
same linked-tail fork at both endpoints. -/
set_option maxHeartbeats 1000000 in
theorem
    profiledRawJointHybridMegaLinkedUnconditional_rightReplacement_both
    (kernelTag : RetainedTag A strategy hwin)
    (owner : ProfiledRawJointHybridOneReplacementOwner A strategy hwin)
    (shadow : TwoShadow A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (inputOne : In₁) (inputTwo : In₂) :
    let mega := MegaLinkedUnconditionalPhysicalController A strategy hwin
      controllers initialBank kernelTag
    let tag := profiledRawJointHybridShadowPhaseLiveRightTag A strategy hwin
      shadow.origin shadow.input
    mega.advanceControls
        ((profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin controllers
            initialBank
              (profiledRawJointHybridMegaLinkedFrontOneOfReplacementOwner A
                strategy hwin controllers initialBank owner), oldOutputOne),
          (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin
            controllers initialBank
              (profiledRawJointHybridMegaLinkedFrontTwoOfShadow A strategy hwin
                controllers initialBank shadow), oldOutputTwo))
        ⟨inputOne, inputTwo, .both⟩ =
      ((profiledRawJointHybridMegaLinkedTailInitialOne A strategy hwin
          controllers initialBank tag, default),
        (profiledRawJointHybridMegaLinkedTailInitialTwo A strategy hwin
          controllers initialBank tag, default)) := by
  rfl

/- Process-two replacement-owner mirror. -/
set_option maxHeartbeats 1000000 in
theorem
    profiledRawJointHybridMegaLinkedUnconditional_leftReplacement_both
    (kernelTag : RetainedTag A strategy hwin)
    (shadow : OneShadow A strategy hwin)
    (owner : ProfiledRawJointHybridTwoReplacementOwner A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (inputOne : In₁) (inputTwo : In₂) :
    let mega := MegaLinkedUnconditionalPhysicalController A strategy hwin
      controllers initialBank kernelTag
    let tag := profiledRawJointHybridShadowPhaseLiveLeftTag A strategy hwin
      shadow.origin shadow.input
    mega.advanceControls
        ((profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin controllers
            initialBank
              (profiledRawJointHybridMegaLinkedFrontOneOfShadow A strategy hwin
                controllers initialBank shadow), oldOutputOne),
          (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin
            controllers initialBank
              (profiledRawJointHybridMegaLinkedFrontTwoOfReplacementOwner A
                strategy hwin controllers initialBank owner), oldOutputTwo))
        ⟨inputOne, inputTwo, .both⟩ =
      ((profiledRawJointHybridMegaLinkedTailInitialOne A strategy hwin
          controllers initialBank tag, default),
        (profiledRawJointHybridMegaLinkedTailInitialTwo A strategy hwin
          controllers initialBank tag, default)) := by
  rfl

/- A genuine strict-right `.both` front pair reaches the closed linked tail
in one physical step.  The old Moore outputs and the legacy kernel tag are
irrelevant; both new local states carry the exact common marked child. -/
set_option maxHeartbeats 1000000 in
theorem
    profiledRawJointHybridMegaLinkedUnconditional_rightEntry_both
    (kernelTag : RetainedTag A strategy hwin)
    (shadow : TwoShadow A strategy hwin)
    (owner : RightGuardOwner A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (inputOne : In₁) (inputTwo : In₂) :
    let entryTag :=
      profiledRawJointHybridMegaLinkedRightEntryRetainedTag A strategy hwin
        shadow owner inputOne inputTwo
    let mega := MegaLinkedUnconditionalPhysicalController A strategy hwin
      controllers initialBank kernelTag
    let entryState :=
      profiledRawJointHybridMegaLinkedRightEntryTailPhysicalPair A strategy
        hwin controllers initialBank shadow owner inputOne inputTwo
    mega.advanceControls
        ((profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin controllers
            initialBank
            (profiledRawJointHybridMegaLinkedFrontOneOfRightGuardOwner A
              strategy hwin controllers initialBank owner), oldOutputOne),
          (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin
            controllers initialBank
            (profiledRawJointHybridMegaLinkedFrontTwoOfShadow A strategy hwin
              controllers initialBank shadow), oldOutputTwo))
        ⟨inputOne, inputTwo, .both⟩ =
      profiledRawJointHybridMegaLinkedEmbedTailPhysicalPair A strategy hwin
        controllers initialBank entryTag
          (MegaLinkedClosedMaps A strategy hwin controllers initialBank)
            entryState := by
  rfl

/- Strict-left simultaneous entry mirror. -/
set_option maxHeartbeats 1000000 in
theorem
    profiledRawJointHybridMegaLinkedUnconditional_leftEntry_both
    (kernelTag : RetainedTag A strategy hwin)
    (shadow : OneShadow A strategy hwin)
    (owner : LeftGuardOwner A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (inputOne : In₁) (inputTwo : In₂) :
    let entryTag :=
      profiledRawJointHybridMegaLinkedLeftEntryRetainedTag A strategy hwin
        shadow owner inputOne inputTwo
    let mega := MegaLinkedUnconditionalPhysicalController A strategy hwin
      controllers initialBank kernelTag
    let entryState :=
      profiledRawJointHybridMegaLinkedLeftEntryTailPhysicalPair A strategy hwin
        controllers initialBank shadow owner inputOne inputTwo
    mega.advanceControls
        ((profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin controllers
            initialBank
            (profiledRawJointHybridMegaLinkedFrontOneOfShadow A strategy hwin
              controllers initialBank shadow), oldOutputOne),
          (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin
            controllers initialBank
            (profiledRawJointHybridMegaLinkedFrontTwoOfLeftGuardOwner A strategy
              hwin controllers initialBank owner), oldOutputTwo))
        ⟨inputOne, inputTwo, .both⟩ =
      profiledRawJointHybridMegaLinkedEmbedTailPhysicalPair A strategy hwin
        controllers initialBank entryTag
          (MegaLinkedClosedMaps A strategy hwin controllers initialBank)
            entryState := by
  rfl

/-! ## The mixed phase closes to a genuine linked pair

These are the promised reachable-seam equations.  Suppose process one already
carries a left-created tag and process two is still in the old front.  On the
first round in which process two receives (`right` or `both`), the resulting
mega state is exactly the embedding of one ordinary linked-controller step
from the delivered process-one state and the canonical not-yet-received
process-two state.  The old front state and its previous output disappear.
The mirror statements cover a right-created tag.

Consequently the next state is in the closed tail/tail region, where the
all-graph conjugacy theorem below applies forever. -/

set_option maxHeartbeats 1000000 in
theorem profiledRawJointHybridMegaLinkedCloseLeftMixed_strictRight
    (entryTag : RetainedTag A strategy hwin)
    (maps : ProfiledRawJointHybridMegaLinkedFrontReceiveMaps A strategy hwin
      controllers initialBank)
    (one : (LinkedTailPhysicalController A strategy hwin entryTag).OneControl)
    (frontTwo : OldTwo A strategy hwin controllers initialBank)
    (frontOutputTwo : Out₂) (inputOne : In₁) (inputTwo : In₂) :
    (MegaLinkedPhysicalController A strategy hwin controllers initialBank
        entryTag maps).advanceControls
        (profiledRawJointHybridMegaLinkedEmbedTailPhysicalOne A strategy hwin
            controllers initialBank entryTag maps one,
          (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin
            controllers initialBank frontTwo, frontOutputTwo))
        ⟨inputOne, inputTwo, .right⟩ =
      profiledRawJointHybridMegaLinkedEmbedTailPhysicalPair A strategy hwin
        controllers initialBank entryTag maps
        ((LinkedTailPhysicalController A strategy hwin entryTag).advanceControls
          (one,
            (LinkedTailPhysicalController A strategy hwin entryTag).initialTwo)
          ⟨inputOne, inputTwo, .right⟩) := by
  cases frontTwo <;> rfl

set_option maxHeartbeats 1000000 in
theorem profiledRawJointHybridMegaLinkedCloseLeftMixed_both
    (entryTag : RetainedTag A strategy hwin)
    (maps : ProfiledRawJointHybridMegaLinkedFrontReceiveMaps A strategy hwin
      controllers initialBank)
    (one : (LinkedTailPhysicalController A strategy hwin entryTag).OneControl)
    (frontTwo : OldTwo A strategy hwin controllers initialBank)
    (frontOutputTwo : Out₂) (inputOne : In₁) (inputTwo : In₂) :
    (MegaLinkedPhysicalController A strategy hwin controllers initialBank
        entryTag maps).advanceControls
        (profiledRawJointHybridMegaLinkedEmbedTailPhysicalOne A strategy hwin
            controllers initialBank entryTag maps one,
          (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin
            controllers initialBank frontTwo, frontOutputTwo))
        ⟨inputOne, inputTwo, .both⟩ =
      profiledRawJointHybridMegaLinkedEmbedTailPhysicalPair A strategy hwin
        controllers initialBank entryTag maps
        ((LinkedTailPhysicalController A strategy hwin entryTag).advanceControls
          (one,
            (LinkedTailPhysicalController A strategy hwin entryTag).initialTwo)
          ⟨inputOne, inputTwo, .both⟩) := by
  cases frontTwo <;> rfl

set_option maxHeartbeats 1000000 in
theorem profiledRawJointHybridMegaLinkedCloseRightMixed_strictLeft
    (entryTag : RetainedTag A strategy hwin)
    (maps : ProfiledRawJointHybridMegaLinkedFrontReceiveMaps A strategy hwin
      controllers initialBank)
    (two : (LinkedTailPhysicalController A strategy hwin entryTag).TwoControl)
    (frontOne : OldOne A strategy hwin controllers initialBank)
    (frontOutputOne : Out₁) (inputOne : In₁) (inputTwo : In₂) :
    (MegaLinkedPhysicalController A strategy hwin controllers initialBank
        entryTag maps).advanceControls
        ((profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin
            controllers initialBank frontOne, frontOutputOne),
          profiledRawJointHybridMegaLinkedEmbedTailPhysicalTwo A strategy hwin
            controllers initialBank entryTag maps two)
        ⟨inputOne, inputTwo, .left⟩ =
      profiledRawJointHybridMegaLinkedEmbedTailPhysicalPair A strategy hwin
        controllers initialBank entryTag maps
        ((LinkedTailPhysicalController A strategy hwin entryTag).advanceControls
          ((LinkedTailPhysicalController A strategy hwin entryTag).initialOne,
            two) ⟨inputOne, inputTwo, .left⟩) := by
  cases frontOne <;> rfl

set_option maxHeartbeats 1000000 in
theorem profiledRawJointHybridMegaLinkedCloseRightMixed_both
    (entryTag : RetainedTag A strategy hwin)
    (maps : ProfiledRawJointHybridMegaLinkedFrontReceiveMaps A strategy hwin
      controllers initialBank)
    (two : (LinkedTailPhysicalController A strategy hwin entryTag).TwoControl)
    (frontOne : OldOne A strategy hwin controllers initialBank)
    (frontOutputOne : Out₁) (inputOne : In₁) (inputTwo : In₂) :
    (MegaLinkedPhysicalController A strategy hwin controllers initialBank
        entryTag maps).advanceControls
        ((profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin
            controllers initialBank frontOne, frontOutputOne),
          profiledRawJointHybridMegaLinkedEmbedTailPhysicalTwo A strategy hwin
            controllers initialBank entryTag maps two)
        ⟨inputOne, inputTwo, .both⟩ =
      profiledRawJointHybridMegaLinkedEmbedTailPhysicalPair A strategy hwin
        controllers initialBank entryTag maps
        ((LinkedTailPhysicalController A strategy hwin entryTag).advanceControls
          ((LinkedTailPhysicalController A strategy hwin entryTag).initialOne,
            two) ⟨inputOne, inputTwo, .both⟩) := by
  cases frontOne <;> rfl

@[simp] theorem profiledRawJointHybridMegaLinkedEmbedTailPhysicalOne_output
    (fallbackTag : RetainedTag A strategy hwin)
    (maps : ProfiledRawJointHybridMegaLinkedFrontReceiveMaps A strategy hwin
      controllers initialBank)
    (state :
      (LinkedTailPhysicalController A strategy hwin fallbackTag).OneControl) :
    (MegaLinkedPhysicalController A strategy hwin controllers initialBank
        fallbackTag maps).outputOne
        (profiledRawJointHybridMegaLinkedEmbedTailPhysicalOne A strategy hwin
          controllers initialBank fallbackTag maps state) =
      (LinkedTailPhysicalController A strategy hwin fallbackTag).outputOne
        state :=
  rfl

@[simp] theorem profiledRawJointHybridMegaLinkedEmbedTailPhysicalTwo_output
    (fallbackTag : RetainedTag A strategy hwin)
    (maps : ProfiledRawJointHybridMegaLinkedFrontReceiveMaps A strategy hwin
      controllers initialBank)
    (state :
      (LinkedTailPhysicalController A strategy hwin fallbackTag).TwoControl) :
    (MegaLinkedPhysicalController A strategy hwin controllers initialBank
        fallbackTag maps).outputTwo
        (profiledRawJointHybridMegaLinkedEmbedTailPhysicalTwo A strategy hwin
          controllers initialBank fallbackTag maps state) =
      (LinkedTailPhysicalController A strategy hwin fallbackTag).outputTwo
        state :=
  rfl

/-- Every linked-tail physical round commutes with its embedding into the
mega controller.  This covers strict-left, strict-right, and simultaneous
rounds uniformly and is independent of all front totalization maps. -/
theorem profiledRawJointHybridMegaLinkedEmbedTail_advanceControls
    (fallbackTag : RetainedTag A strategy hwin)
    (maps : ProfiledRawJointHybridMegaLinkedFrontReceiveMaps A strategy hwin
      controllers initialBank)
    (state :
      (LinkedTailPhysicalController A strategy hwin fallbackTag).OneControl ×
        (LinkedTailPhysicalController A strategy hwin fallbackTag).TwoControl)
    (round : EnvironmentRound In₁ In₂) :
    (MegaLinkedPhysicalController A strategy hwin controllers initialBank
        fallbackTag maps).advanceControls
        (profiledRawJointHybridMegaLinkedEmbedTailPhysicalOne A strategy hwin
            controllers initialBank fallbackTag maps state.1,
          profiledRawJointHybridMegaLinkedEmbedTailPhysicalTwo A strategy hwin
            controllers initialBank fallbackTag maps state.2)
        round =
      (profiledRawJointHybridMegaLinkedEmbedTailPhysicalOne A strategy hwin
          controllers initialBank fallbackTag maps
          ((LinkedTailPhysicalController A strategy hwin fallbackTag
            ).advanceControls state round).1,
        profiledRawJointHybridMegaLinkedEmbedTailPhysicalTwo A strategy hwin
          controllers initialBank fallbackTag maps
          ((LinkedTailPhysicalController A strategy hwin fallbackTag
            ).advanceControls state round).2) := by
  rcases round with ⟨inputOne, inputTwo, graph⟩
  cases graph <;> rfl

/-- Rerooting both physical machines at corresponding tail states preserves
the embedding at every finite time.  This is deliberately stated for an
arbitrary tail state; identifying the entry state with the canonical initial
tail is the separate front/mixed handoff obligation. -/
theorem profiledRawJointHybridMegaLinkedEmbedTail_globalStateTrace
    (fallbackTag : RetainedTag A strategy hwin)
    (maps : ProfiledRawJointHybridMegaLinkedFrontReceiveMaps A strategy hwin
      controllers initialBank)
    (state :
      (LinkedTailPhysicalController A strategy hwin fallbackTag).OneControl ×
        (LinkedTailPhysicalController A strategy hwin fallbackTag).TwoControl)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    ((MegaLinkedPhysicalController A strategy hwin controllers initialBank
          fallbackTag maps).globalMachine.reroot
        (profiledRawJointHybridMegaLinkedEmbedTailPhysicalPair A strategy hwin
          controllers initialBank fallbackTag maps state)).globalStateTrace
          env n =
      profiledRawJointHybridMegaLinkedEmbedTailPhysicalPair A strategy hwin
        controllers initialBank fallbackTag maps
        (((LinkedTailPhysicalController A strategy hwin fallbackTag
            ).globalMachine.reroot state).globalStateTrace env n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [FiniteGlobalRoundMachine.globalStateTrace_succ,
        FiniteGlobalRoundMachine.globalStateTrace_succ, ih]
      exact profiledRawJointHybridMegaLinkedEmbedTail_advanceControls A
        strategy hwin controllers initialBank fallbackTag maps _ _

/-- The Moore word of any rerooted linked-tail suffix is unchanged by the
mega embedding.  Canonical reference-word alignment can therefore be
transported as soon as the front proof identifies the concrete entry pair. -/
theorem profiledRawJointHybridMegaLinkedEmbedTail_globalMachineTraceWord
    (fallbackTag : RetainedTag A strategy hwin)
    (maps : ProfiledRawJointHybridMegaLinkedFrontReceiveMaps A strategy hwin
      controllers initialBank)
    (state :
      (LinkedTailPhysicalController A strategy hwin fallbackTag).OneControl ×
        (LinkedTailPhysicalController A strategy hwin fallbackTag).TwoControl)
    (env : EnvironmentSequence In₁ In₂) :
    ((MegaLinkedPhysicalController A strategy hwin controllers initialBank
          fallbackTag maps).globalMachine.reroot
        (profiledRawJointHybridMegaLinkedEmbedTailPhysicalPair A strategy hwin
          controllers initialBank fallbackTag maps state)
      ).globalMachineTraceWord
        (MegaLinkedPhysicalController A strategy hwin controllers initialBank
          fallbackTag maps).globalOutputOne
        (MegaLinkedPhysicalController A strategy hwin controllers initialBank
          fallbackTag maps).globalOutputTwo env =
      ((LinkedTailPhysicalController A strategy hwin fallbackTag
          ).globalMachine.reroot state).globalMachineTraceWord
        (LinkedTailPhysicalController A strategy hwin fallbackTag
          ).globalOutputOne
        (LinkedTailPhysicalController A strategy hwin fallbackTag
          ).globalOutputTwo env := by
  funext n
  simp only [FiniteGlobalRoundMachine.globalMachineTraceWord]
  rw [profiledRawJointHybridMegaLinkedEmbedTail_globalStateTrace A strategy
    hwin controllers initialBank fallbackTag maps state env (n + 1)]
  rfl

/-- Extensional form of the embedding theorem, convenient when an earlier
front/mixed calculation establishes the embedded-state equality. -/
theorem
    profiledRawJointHybridMegaLinked_globalMachineTraceWord_of_eq_embed
    (fallbackTag : RetainedTag A strategy hwin)
    (maps : ProfiledRawJointHybridMegaLinkedFrontReceiveMaps A strategy hwin
      controllers initialBank)
    (megaState :
      (MegaLinkedPhysicalController A strategy hwin controllers initialBank
          fallbackTag maps).OneControl ×
        (MegaLinkedPhysicalController A strategy hwin controllers initialBank
          fallbackTag maps).TwoControl)
    (linkedState :
      (LinkedTailPhysicalController A strategy hwin fallbackTag).OneControl ×
        (LinkedTailPhysicalController A strategy hwin fallbackTag).TwoControl)
    (hstate : megaState =
      profiledRawJointHybridMegaLinkedEmbedTailPhysicalPair A strategy hwin
        controllers initialBank fallbackTag maps linkedState)
    (env : EnvironmentSequence In₁ In₂) :
    ((MegaLinkedPhysicalController A strategy hwin controllers initialBank
          fallbackTag maps).globalMachine.reroot megaState
      ).globalMachineTraceWord
        (MegaLinkedPhysicalController A strategy hwin controllers initialBank
          fallbackTag maps).globalOutputOne
        (MegaLinkedPhysicalController A strategy hwin controllers initialBank
          fallbackTag maps).globalOutputTwo env =
      ((LinkedTailPhysicalController A strategy hwin fallbackTag
          ).globalMachine.reroot linkedState).globalMachineTraceWord
        (LinkedTailPhysicalController A strategy hwin fallbackTag
          ).globalOutputOne
        (LinkedTailPhysicalController A strategy hwin fallbackTag
          ).globalOutputTwo env := by
  subst megaState
  exact
    profiledRawJointHybridMegaLinkedEmbedTail_globalMachineTraceWord A strategy
      hwin controllers initialBank fallbackTag maps linkedState env

/-! ## Trace splice at a genuine simultaneous front handoff -/

/-- After a canonical strict-right `.both` handoff, the closed mega kernel's
entire future word is the linked-tail word rerooted at the exact entry state.
No reachability or acceptance premise is added. -/
theorem
    profiledRawJointHybridMegaLinkedUnconditional_rightEntry_both_traceSplice
    (kernelTag : RetainedTag A strategy hwin)
    (shadow : TwoShadow A strategy hwin)
    (owner : RightGuardOwner A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (inputOne : In₁) (inputTwo : In₂)
    (env : EnvironmentSequence In₁ In₂) :
    let entryTag :=
      profiledRawJointHybridMegaLinkedRightEntryRetainedTag A strategy hwin
        shadow owner inputOne inputTwo
    let mega := MegaLinkedUnconditionalPhysicalController A strategy hwin
      controllers initialBank kernelTag
    let linked := LinkedTailPhysicalController A strategy hwin entryTag
    let entryState :=
      profiledRawJointHybridMegaLinkedRightEntryTailPhysicalPair A strategy
        hwin controllers initialBank shadow owner inputOne inputTwo
    let frontState :=
      ((profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin controllers
          initialBank
          (profiledRawJointHybridMegaLinkedFrontOneOfRightGuardOwner A strategy
            hwin controllers initialBank owner), oldOutputOne),
        (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin controllers
          initialBank
          (profiledRawJointHybridMegaLinkedFrontTwoOfShadow A strategy hwin
            controllers initialBank shadow), oldOutputTwo))
    let round : EnvironmentRound In₁ In₂ :=
      ⟨inputOne, inputTwo, .both⟩
    (mega.globalMachine.reroot (mega.advanceControls frontState round)
      ).globalMachineTraceWord mega.globalOutputOne mega.globalOutputTwo env =
      (linked.globalMachine.reroot entryState).globalMachineTraceWord
        linked.globalOutputOne linked.globalOutputTwo env := by
  dsimp only
  apply
    profiledRawJointHybridMegaLinked_globalMachineTraceWord_of_eq_embed A
      strategy hwin controllers initialBank
        (profiledRawJointHybridMegaLinkedRightEntryRetainedTag A strategy hwin
          shadow owner inputOne inputTwo)
        (MegaLinkedClosedMaps A strategy hwin controllers initialBank)
        _
        (profiledRawJointHybridMegaLinkedRightEntryTailPhysicalPair A strategy
          hwin controllers initialBank shadow owner inputOne inputTwo)
        (profiledRawJointHybridMegaLinkedUnconditional_rightEntry_both A
          strategy hwin controllers initialBank kernelTag shadow owner
            oldOutputOne oldOutputTwo inputOne inputTwo)
        env

/-- Strict-left `.both` trace-splice mirror. -/
theorem
    profiledRawJointHybridMegaLinkedUnconditional_leftEntry_both_traceSplice
    (kernelTag : RetainedTag A strategy hwin)
    (shadow : OneShadow A strategy hwin)
    (owner : LeftGuardOwner A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (inputOne : In₁) (inputTwo : In₂)
    (env : EnvironmentSequence In₁ In₂) :
    let entryTag :=
      profiledRawJointHybridMegaLinkedLeftEntryRetainedTag A strategy hwin
        shadow owner inputOne inputTwo
    let mega := MegaLinkedUnconditionalPhysicalController A strategy hwin
      controllers initialBank kernelTag
    let linked := LinkedTailPhysicalController A strategy hwin entryTag
    let entryState :=
      profiledRawJointHybridMegaLinkedLeftEntryTailPhysicalPair A strategy hwin
        controllers initialBank shadow owner inputOne inputTwo
    let frontState :=
      ((profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin controllers
          initialBank
          (profiledRawJointHybridMegaLinkedFrontOneOfShadow A strategy hwin
            controllers initialBank shadow), oldOutputOne),
        (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin controllers
          initialBank
          (profiledRawJointHybridMegaLinkedFrontTwoOfLeftGuardOwner A strategy
            hwin controllers initialBank owner), oldOutputTwo))
    let round : EnvironmentRound In₁ In₂ :=
      ⟨inputOne, inputTwo, .both⟩
    (mega.globalMachine.reroot (mega.advanceControls frontState round)
      ).globalMachineTraceWord mega.globalOutputOne mega.globalOutputTwo env =
      (linked.globalMachine.reroot entryState).globalMachineTraceWord
        linked.globalOutputOne linked.globalOutputTwo env := by
  dsimp only
  apply
    profiledRawJointHybridMegaLinked_globalMachineTraceWord_of_eq_embed A
      strategy hwin controllers initialBank
        (profiledRawJointHybridMegaLinkedLeftEntryRetainedTag A strategy hwin
          shadow owner inputOne inputTwo)
        (MegaLinkedClosedMaps A strategy hwin controllers initialBank)
        _
        (profiledRawJointHybridMegaLinkedLeftEntryTailPhysicalPair A strategy
          hwin controllers initialBank shadow owner inputOne inputTwo)
        (profiledRawJointHybridMegaLinkedUnconditional_leftEntry_both A
          strategy hwin controllers initialBank kernelTag shadow owner
            oldOutputOne oldOutputTwo inputOne inputTwo)
        env

/-! ## Eventual conjugacy at the first opposite receive

The current tagged endpoint below is arbitrary, so it already includes any
finite same-direction mixed prefix.  Once the still-front endpoint receives,
the one-step close equations above put both endpoints in the linked tail; the
preceding all-future theorem then gives trace-word equality for every suffix.

These results are intentionally factored through the named linked-controller
constructor.  The constructor used here is the repaired `FullRestart`
controller: after a hierarchy switch its blind no-receive step rebuilds both
the semantic sender and receiver coordinates at the fresh bank child.  The
front/mixed argument remains independent of that proof-side interpretation. -/

theorem profiledRawJointHybridMegaLinkedCloseLeftMixed_suffix
    (entryTag : RetainedTag A strategy hwin)
    (maps : ProfiledRawJointHybridMegaLinkedFrontReceiveMaps A strategy hwin
      controllers initialBank)
    (one : (LinkedTailPhysicalController A strategy hwin entryTag).OneControl)
    (frontTwo : OldTwo A strategy hwin controllers initialBank)
    (frontOutputTwo : Out₂) (inputOne : In₁) (inputTwo : In₂)
    (closingGraph : Graph) (hreceives : closingGraph ≠ .left)
    (env : EnvironmentSequence In₁ In₂) :
    let mega :=
      MegaLinkedPhysicalController A strategy hwin controllers initialBank
        entryTag maps
    let linked := LinkedTailPhysicalController A strategy hwin entryTag
    let round : EnvironmentRound In₁ In₂ :=
      ⟨inputOne, inputTwo, closingGraph⟩
    let mixed :=
      (profiledRawJointHybridMegaLinkedEmbedTailPhysicalOne A strategy hwin
          controllers initialBank entryTag maps one,
        (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin controllers
          initialBank frontTwo, frontOutputTwo))
    let virtual := (one, linked.initialTwo)
    (mega.globalMachine.reroot (mega.advanceControls mixed round)
      ).globalMachineTraceWord mega.globalOutputOne mega.globalOutputTwo env =
      (linked.globalMachine.reroot (linked.advanceControls virtual round)
        ).globalMachineTraceWord linked.globalOutputOne linked.globalOutputTwo
          env := by
  dsimp only
  cases closingGraph with
  | left => exact (hreceives rfl).elim
  | right =>
      exact
        profiledRawJointHybridMegaLinked_globalMachineTraceWord_of_eq_embed A
          strategy hwin controllers initialBank entryTag maps _ _
            (profiledRawJointHybridMegaLinkedCloseLeftMixed_strictRight A
              strategy hwin controllers initialBank entryTag maps one frontTwo
                frontOutputTwo inputOne inputTwo) env
  | both =>
      exact
        profiledRawJointHybridMegaLinked_globalMachineTraceWord_of_eq_embed A
          strategy hwin controllers initialBank entryTag maps _ _
            (profiledRawJointHybridMegaLinkedCloseLeftMixed_both A strategy
              hwin controllers initialBank entryTag maps one frontTwo
                frontOutputTwo inputOne inputTwo) env

/-- Right-created mirror. -/
theorem profiledRawJointHybridMegaLinkedCloseRightMixed_suffix
    (entryTag : RetainedTag A strategy hwin)
    (maps : ProfiledRawJointHybridMegaLinkedFrontReceiveMaps A strategy hwin
      controllers initialBank)
    (two : (LinkedTailPhysicalController A strategy hwin entryTag).TwoControl)
    (frontOne : OldOne A strategy hwin controllers initialBank)
    (frontOutputOne : Out₁) (inputOne : In₁) (inputTwo : In₂)
    (closingGraph : Graph) (hreceives : closingGraph ≠ .right)
    (env : EnvironmentSequence In₁ In₂) :
    let mega :=
      MegaLinkedPhysicalController A strategy hwin controllers initialBank
        entryTag maps
    let linked := LinkedTailPhysicalController A strategy hwin entryTag
    let round : EnvironmentRound In₁ In₂ :=
      ⟨inputOne, inputTwo, closingGraph⟩
    let mixed :=
      ((profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin controllers
          initialBank frontOne, frontOutputOne),
        profiledRawJointHybridMegaLinkedEmbedTailPhysicalTwo A strategy hwin
          controllers initialBank entryTag maps two)
    let virtual := (linked.initialOne, two)
    (mega.globalMachine.reroot (mega.advanceControls mixed round)
      ).globalMachineTraceWord mega.globalOutputOne mega.globalOutputTwo env =
      (linked.globalMachine.reroot (linked.advanceControls virtual round)
        ).globalMachineTraceWord linked.globalOutputOne linked.globalOutputTwo
          env := by
  dsimp only
  cases closingGraph with
  | left =>
      exact
        profiledRawJointHybridMegaLinked_globalMachineTraceWord_of_eq_embed A
          strategy hwin controllers initialBank entryTag maps _ _
            (profiledRawJointHybridMegaLinkedCloseRightMixed_strictLeft A
              strategy hwin controllers initialBank entryTag maps two frontOne
                frontOutputOne inputOne inputTwo) env
  | right => exact (hreceives rfl).elim
  | both =>
      exact
        profiledRawJointHybridMegaLinked_globalMachineTraceWord_of_eq_embed A
          strategy hwin controllers initialBank entryTag maps _ _
            (profiledRawJointHybridMegaLinkedCloseRightMixed_both A strategy
              hwin controllers initialBank entryTag maps two frontOne
                frontOutputOne inputOne inputTwo) env

/-! ## Closed-kernel form of the first opposite receive

The preceding mixed-state theorems were deliberately proved for arbitrary
compatibility tables.  The two wrappers below are the operational form used
by the completed controller: there is no receive-map argument, and the
legacy kernel tag may differ from the tag carried by the reached mixed
state.  Tag irrelevance changes only that proof-side totalization parameter;
the locally carried entry tag remains untouched. -/

/-- A left-created mixed state closes at its first process-two receive, for
the unconditional leader-free mega kernel. -/
theorem
    profiledRawJointHybridMegaLinkedUnconditional_closeLeftMixed_traceSplice
    (entryTag : RetainedTag A strategy hwin)
    (one : (LinkedTailPhysicalController A strategy hwin entryTag).OneControl)
    (frontTwo : OldTwo A strategy hwin controllers initialBank)
    (frontOutputTwo : Out₂) (inputOne : In₁) (inputTwo : In₂)
    (closingGraph : Graph) (hreceives : closingGraph ≠ .left)
    (env : EnvironmentSequence In₁ In₂) :
    let mega :=
      MegaLinkedUnconditionalPhysicalController A strategy hwin controllers
        initialBank entryTag
    let linked := LinkedTailPhysicalController A strategy hwin entryTag
    let round : EnvironmentRound In₁ In₂ :=
      ⟨inputOne, inputTwo, closingGraph⟩
    let mixed :=
      (profiledRawJointHybridMegaLinkedEmbedTailPhysicalOne A strategy hwin
          controllers initialBank entryTag
            (MegaLinkedClosedMaps A strategy hwin controllers initialBank) one,
        (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin controllers
          initialBank frontTwo, frontOutputTwo))
    let virtual := (one, linked.initialTwo)
    (mega.globalMachine.reroot (mega.advanceControls mixed round)
      ).globalMachineTraceWord mega.globalOutputOne mega.globalOutputTwo env =
      (linked.globalMachine.reroot (linked.advanceControls virtual round)
        ).globalMachineTraceWord linked.globalOutputOne linked.globalOutputTwo
          env := by
  dsimp only
  exact
    profiledRawJointHybridMegaLinkedCloseLeftMixed_suffix A strategy hwin
      controllers initialBank entryTag
        (MegaLinkedClosedMaps A strategy hwin controllers initialBank) one
          frontTwo frontOutputTwo inputOne inputTwo closingGraph hreceives env

/-- Right-created mirror. -/
theorem
    profiledRawJointHybridMegaLinkedUnconditional_closeRightMixed_traceSplice
    (entryTag : RetainedTag A strategy hwin)
    (two : (LinkedTailPhysicalController A strategy hwin entryTag).TwoControl)
    (frontOne : OldOne A strategy hwin controllers initialBank)
    (frontOutputOne : Out₁) (inputOne : In₁) (inputTwo : In₂)
    (closingGraph : Graph) (hreceives : closingGraph ≠ .right)
    (env : EnvironmentSequence In₁ In₂) :
    let mega :=
      MegaLinkedUnconditionalPhysicalController A strategy hwin controllers
        initialBank entryTag
    let linked := LinkedTailPhysicalController A strategy hwin entryTag
    let round : EnvironmentRound In₁ In₂ :=
      ⟨inputOne, inputTwo, closingGraph⟩
    let mixed :=
      ((profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin controllers
          initialBank frontOne, frontOutputOne),
        profiledRawJointHybridMegaLinkedEmbedTailPhysicalTwo A strategy hwin
          controllers initialBank entryTag
            (MegaLinkedClosedMaps A strategy hwin controllers initialBank) two)
    let virtual := (linked.initialOne, two)
    (mega.globalMachine.reroot (mega.advanceControls mixed round)
      ).globalMachineTraceWord mega.globalOutputOne mega.globalOutputTwo env =
      (linked.globalMachine.reroot (linked.advanceControls virtual round)
        ).globalMachineTraceWord linked.globalOutputOne linked.globalOutputTwo
          env := by
  dsimp only
  exact
    profiledRawJointHybridMegaLinkedCloseRightMixed_suffix A strategy hwin
      controllers initialBank entryTag
        (MegaLinkedClosedMaps A strategy hwin controllers initialBank) two
          frontOne frontOutputOne inputOne inputTwo closingGraph hreceives env

/-- At the exact canonical entry pair, the rerooted mega suffix is therefore
the verified linked-deferred reference word.  This closes the suffix/splice
half of the handoff; only reachability of this entry pair from the finite
front remains upstream. -/
theorem
    profiledRawJointHybridMegaLinkedCanonicalTailSuffix_eq_referenceWord
    (entryTag : RetainedTag A strategy hwin)
    (maps : ProfiledRawJointHybridMegaLinkedFrontReceiveMaps A strategy hwin
      controllers initialBank)
    (env : EnvironmentSequence In₁ In₂) :
    let tailController :=
      LinkedTailPhysicalController A strategy hwin entryTag
    let tailInitial :=
      (tailController.initialOne, tailController.initialTwo)
    ((MegaLinkedPhysicalController A strategy hwin controllers initialBank
          entryTag maps).globalMachine.reroot
        (profiledRawJointHybridMegaLinkedEmbedTailPhysicalPair A strategy hwin
          controllers initialBank entryTag maps tailInitial)
      ).globalMachineTraceWord
        (MegaLinkedPhysicalController A strategy hwin controllers initialBank
          entryTag maps).globalOutputOne
        (MegaLinkedPhysicalController A strategy hwin controllers initialBank
          entryTag maps).globalOutputTwo env =
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartTraceInvariant
        A strategy hwin entryTag env).referenceWord tailController := by
  dsimp only
  rw [profiledRawJointHybridMegaLinkedEmbedTail_globalMachineTraceWord A
    strategy hwin controllers initialBank entryTag maps
      ((LinkedTailPhysicalController A strategy hwin entryTag).initialOne,
        (LinkedTailPhysicalController A strategy hwin entryTag).initialTwo)
      env]
  exact
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartTraceWord_eq_referenceWord
      A strategy hwin entryTag env

/-! ## Finite-prefix splice into the repaired tail -/

/-- Suppose an arbitrary finite run of the closed mega controller reaches the
genuine strict-right front pair at time `start`, and that round is the
simultaneous handoff.  Dropping the completed prefix (`start + 1` rounds) from
the mega word gives exactly the `FullRestart` tail rerooted at the concrete
entry state.  This is a trace statement only; it introduces no acceptance
premise. -/
theorem
    profiledRawJointHybridMegaLinkedUnconditional_rightEntry_both_finitePrefix_traceSplice
    (kernelTag : RetainedTag A strategy hwin)
    (shadow : TwoShadow A strategy hwin)
    (owner : RightGuardOwner A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (env : EnvironmentSequence In₁ In₂) (start : Nat)
    (hstate :
      (MegaLinkedUnconditionalPhysicalController A strategy hwin controllers
          initialBank kernelTag).globalMachine.globalStateTrace env start =
        ((profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin
            controllers initialBank
            (profiledRawJointHybridMegaLinkedFrontOneOfRightGuardOwner A
              strategy hwin controllers initialBank owner), oldOutputOne),
          (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin
            controllers initialBank
            (profiledRawJointHybridMegaLinkedFrontTwoOfShadow A strategy hwin
              controllers initialBank shadow), oldOutputTwo)))
    (hgraph : (env start).graph = .both) :
    let inputOne := (env start).inputOne
    let inputTwo := (env start).inputTwo
    let entryTag :=
      profiledRawJointHybridMegaLinkedRightEntryRetainedTag A strategy hwin
        shadow owner inputOne inputTwo
    let mega :=
      MegaLinkedUnconditionalPhysicalController A strategy hwin controllers
        initialBank kernelTag
    let linked := LinkedTailPhysicalController A strategy hwin entryTag
    let entryState :=
      profiledRawJointHybridMegaLinkedRightEntryTailPhysicalPair A strategy
        hwin controllers initialBank shadow owner inputOne inputTwo
    OmegaWord.drop
        (mega.globalMachine.globalMachineTraceWord mega.globalOutputOne
          mega.globalOutputTwo env) (start + 1) =
      (linked.globalMachine.reroot entryState).globalMachineTraceWord
        linked.globalOutputOne linked.globalOutputTwo
          (OmegaWord.drop env (start + 1)) := by
  dsimp only
  let mega :=
    MegaLinkedUnconditionalPhysicalController A strategy hwin controllers
      initialBank kernelTag
  let inputOne := (env start).inputOne
  let inputTwo := (env start).inputTwo
  let entryTag :=
    profiledRawJointHybridMegaLinkedRightEntryRetainedTag A strategy hwin
      shadow owner inputOne inputTwo
  let linked := LinkedTailPhysicalController A strategy hwin entryTag
  let entryState :=
    profiledRawJointHybridMegaLinkedRightEntryTailPhysicalPair A strategy hwin
      controllers initialBank shadow owner inputOne inputTwo
  let frontState :=
    ((profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin controllers
        initialBank
        (profiledRawJointHybridMegaLinkedFrontOneOfRightGuardOwner A strategy
          hwin controllers initialBank owner), oldOutputOne),
      (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin controllers
        initialBank
        (profiledRawJointHybridMegaLinkedFrontTwoOfShadow A strategy hwin
          controllers initialBank shadow), oldOutputTwo))
  let round : EnvironmentRound In₁ In₂ := ⟨inputOne, inputTwo, .both⟩
  have hround : env start = round := by
    rcases henv : env start with ⟨i₁, i₂, graph⟩
    have hgraph' : graph = .both := by simpa [henv] using hgraph
    subst graph
    simp [round, inputOne, inputTwo, henv]
  have hnext :
      mega.globalMachine.globalStateTrace env (start + 1) =
        mega.advanceControls frontState round := by
    rw [FiniteGlobalRoundMachine.globalStateTrace_succ, hstate, hround]
    rfl
  have hreroot :=
    mega.globalMachine.reroot_globalMachineTraceWord_drop mega.globalOutputOne
      mega.globalOutputTwo env (start + 1)
  have hsplice :=
    profiledRawJointHybridMegaLinkedUnconditional_rightEntry_both_traceSplice A
      strategy hwin controllers initialBank kernelTag shadow owner oldOutputOne
        oldOutputTwo inputOne inputTwo (OmegaWord.drop env (start + 1))
  calc
    OmegaWord.drop
          (mega.globalMachine.globalMachineTraceWord mega.globalOutputOne
            mega.globalOutputTwo env) (start + 1) =
        (mega.globalMachine.reroot
          (mega.globalMachine.globalStateTrace env (start + 1))
        ).globalMachineTraceWord mega.globalOutputOne mega.globalOutputTwo
          (OmegaWord.drop env (start + 1)) := hreroot.symm
    _ =
        (mega.globalMachine.reroot (mega.advanceControls frontState round)
        ).globalMachineTraceWord mega.globalOutputOne mega.globalOutputTwo
          (OmegaWord.drop env (start + 1)) := by rw [hnext]
    _ =
        (linked.globalMachine.reroot entryState).globalMachineTraceWord
          linked.globalOutputOne linked.globalOutputTwo
            (OmegaWord.drop env (start + 1)) := by
      simpa [mega, linked, entryTag, entryState, frontState, round, inputOne,
        inputTwo] using hsplice

/-- Strict-left simultaneous-handoff mirror. -/
theorem
    profiledRawJointHybridMegaLinkedUnconditional_leftEntry_both_finitePrefix_traceSplice
    (kernelTag : RetainedTag A strategy hwin)
    (shadow : OneShadow A strategy hwin)
    (owner : LeftGuardOwner A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (env : EnvironmentSequence In₁ In₂) (start : Nat)
    (hstate :
      (MegaLinkedUnconditionalPhysicalController A strategy hwin controllers
          initialBank kernelTag).globalMachine.globalStateTrace env start =
        ((profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin
            controllers initialBank
            (profiledRawJointHybridMegaLinkedFrontOneOfShadow A strategy hwin
              controllers initialBank shadow), oldOutputOne),
          (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin
            controllers initialBank
            (profiledRawJointHybridMegaLinkedFrontTwoOfLeftGuardOwner A
              strategy hwin controllers initialBank owner), oldOutputTwo)))
    (hgraph : (env start).graph = .both) :
    let inputOne := (env start).inputOne
    let inputTwo := (env start).inputTwo
    let entryTag :=
      profiledRawJointHybridMegaLinkedLeftEntryRetainedTag A strategy hwin
        shadow owner inputOne inputTwo
    let mega :=
      MegaLinkedUnconditionalPhysicalController A strategy hwin controllers
        initialBank kernelTag
    let linked := LinkedTailPhysicalController A strategy hwin entryTag
    let entryState :=
      profiledRawJointHybridMegaLinkedLeftEntryTailPhysicalPair A strategy
        hwin controllers initialBank shadow owner inputOne inputTwo
    OmegaWord.drop
        (mega.globalMachine.globalMachineTraceWord mega.globalOutputOne
          mega.globalOutputTwo env) (start + 1) =
      (linked.globalMachine.reroot entryState).globalMachineTraceWord
        linked.globalOutputOne linked.globalOutputTwo
          (OmegaWord.drop env (start + 1)) := by
  dsimp only
  let mega :=
    MegaLinkedUnconditionalPhysicalController A strategy hwin controllers
      initialBank kernelTag
  let inputOne := (env start).inputOne
  let inputTwo := (env start).inputTwo
  let entryTag :=
    profiledRawJointHybridMegaLinkedLeftEntryRetainedTag A strategy hwin
      shadow owner inputOne inputTwo
  let linked := LinkedTailPhysicalController A strategy hwin entryTag
  let entryState :=
    profiledRawJointHybridMegaLinkedLeftEntryTailPhysicalPair A strategy hwin
      controllers initialBank shadow owner inputOne inputTwo
  let frontState :=
    ((profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin controllers
        initialBank
        (profiledRawJointHybridMegaLinkedFrontOneOfShadow A strategy hwin
          controllers initialBank shadow), oldOutputOne),
      (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin controllers
        initialBank
        (profiledRawJointHybridMegaLinkedFrontTwoOfLeftGuardOwner A strategy
          hwin controllers initialBank owner), oldOutputTwo))
  let round : EnvironmentRound In₁ In₂ := ⟨inputOne, inputTwo, .both⟩
  have hround : env start = round := by
    rcases henv : env start with ⟨i₁, i₂, graph⟩
    have hgraph' : graph = .both := by simpa [henv] using hgraph
    subst graph
    simp [round, inputOne, inputTwo, henv]
  have hnext :
      mega.globalMachine.globalStateTrace env (start + 1) =
        mega.advanceControls frontState round := by
    rw [FiniteGlobalRoundMachine.globalStateTrace_succ, hstate, hround]
    rfl
  have hreroot :=
    mega.globalMachine.reroot_globalMachineTraceWord_drop mega.globalOutputOne
      mega.globalOutputTwo env (start + 1)
  have hsplice :=
    profiledRawJointHybridMegaLinkedUnconditional_leftEntry_both_traceSplice A
      strategy hwin controllers initialBank kernelTag shadow owner oldOutputOne
        oldOutputTwo inputOne inputTwo (OmegaWord.drop env (start + 1))
  calc
    OmegaWord.drop
          (mega.globalMachine.globalMachineTraceWord mega.globalOutputOne
            mega.globalOutputTwo env) (start + 1) =
        (mega.globalMachine.reroot
          (mega.globalMachine.globalStateTrace env (start + 1))
        ).globalMachineTraceWord mega.globalOutputOne mega.globalOutputTwo
          (OmegaWord.drop env (start + 1)) := hreroot.symm
    _ =
        (mega.globalMachine.reroot (mega.advanceControls frontState round)
        ).globalMachineTraceWord mega.globalOutputOne mega.globalOutputTwo
          (OmegaWord.drop env (start + 1)) := by rw [hnext]
    _ =
        (linked.globalMachine.reroot entryState).globalMachineTraceWord
          linked.globalOutputOne linked.globalOutputTwo
            (OmegaWord.drop env (start + 1)) := by
      simpa [mega, linked, entryTag, entryState, frontState, round, inputOne,
        inputTwo] using hsplice

end

end DetParityAutomaton

end DistributedSynthesis
