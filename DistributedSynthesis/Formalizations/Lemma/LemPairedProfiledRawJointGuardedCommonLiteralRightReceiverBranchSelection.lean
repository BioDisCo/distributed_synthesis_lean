/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralFreshReceiveSameOccurrence
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralDeferredMemberAdapters

/-!
# Right-seam receive branch selection

At a receive round, the output emitted now and the fresh delayed poststate are
different pieces of data.  The current output comes from the already selected
old literal-cross tables.  The fresh poststate records the still unresolved
interpretation of the new occurrence:

* a strict-right occurrence starts row `first` with the literal member
  (`false`);
* a simultaneous occurrence starts row `both` with the exact member (`true`).

The two fresh roots use the same literal child key, but they are not identified:
their rows and anchors remain different.  Independently of the old table
members selected at the current receive, the existing anti-mosaic theorem says
that its two physical outputs are exactly the two coordinates of the one
`nextPairAt` cut.  No theorem here attributes that current output to a
transition of the fresh poststate.

All executable controls remain finite.  No runtime map receives a graph,
orientation, leader bit, history, or view.
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

private abbrev CrossValid :=
  ProfiledRawJointGuardedCommonLiteralCrossExtraValid A strategy hwin

namespace ProfiledRawJointGuardedCommonDecoratedPolicyPackage

variable {initial : CommonPoint A strategy}

private abbrev Package (initial : CommonPoint A strategy) :=
  ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy hwin initial
    (CrossValid A strategy hwin)

private abbrev State :=
  ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin initial
    (CrossValid A strategy hwin)

private abbrev RightReceiver
    (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralRightSeamStagedReceiverState A strategy
    hwin package

private abbrev RightPending
    (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralRightSeamPendingSenderCandidate A
    strategy hwin package

private abbrev RightShared
    (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralRightSeamStagedSenderState A strategy
    hwin package

private abbrev RightStage
    (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralRightSeamStage A strategy hwin package

/-! ## The two distinct fresh poststate roots -/

/-- Fresh poststate for a strict-right occurrence.  The receiver records the
literal restart interpretation at row `first`; `false` is stored in its own
finite state and is not read from the current graph. -/
noncomputable def literalRightSeamStrictOpenReceiverRoot
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (incoming blockInput : In₁ × In₂) : RightReceiver A strategy hwin package :=
  package.literalRightSeamStagedReceiverInitial A strategy hwin
    (package.successorLiteralCrossFreshSeamKey A strategy hwin state incoming
      blockInput) .first false

/-- Fresh poststate for a simultaneous occurrence.  It keeps the exact
interpretation at row `both` with the true member anchor. -/
noncomputable def literalRightSeamClosedReceiverRoot
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (incoming blockInput : In₁ × In₂) : RightReceiver A strategy hwin package :=
  package.literalRightSeamStagedReceiverInitial A strategy hwin
    (package.successorLiteralCrossFreshSeamKey A strategy hwin state incoming
      blockInput) .both true

@[simp] theorem literalRightSeamStrictOpenReceiverRoot_key
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (incoming blockInput : In₁ × In₂) :
    (package.literalRightSeamStrictOpenReceiverRoot A strategy hwin state
      incoming blockInput).1 =
      package.successorLiteralCrossFreshSeamKey A strategy hwin state incoming
        blockInput :=
  rfl

@[simp] theorem literalRightSeamClosedReceiverRoot_key
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (incoming blockInput : In₁ × In₂) :
    (package.literalRightSeamClosedReceiverRoot A strategy hwin state incoming
      blockInput).1 =
      package.successorLiteralCrossFreshSeamKey A strategy hwin state incoming
        blockInput :=
  rfl

@[simp] theorem literalRightSeamStrictOpenReceiverRoot_row
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (incoming blockInput : In₁ × In₂) :
    (package.literalRightSeamStrictOpenReceiverRoot A strategy hwin state
      incoming blockInput).2.1 = .first :=
  rfl

@[simp] theorem literalRightSeamClosedReceiverRoot_row
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (incoming blockInput : In₁ × In₂) :
    (package.literalRightSeamClosedReceiverRoot A strategy hwin state incoming
      blockInput).2.1 = .both :=
  rfl

@[simp] theorem literalRightSeamStrictOpenReceiverRoot_anchor
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (incoming blockInput : In₁ × In₂) :
    (package.literalRightSeamStrictOpenReceiverRoot A strategy hwin state
      incoming blockInput).2.2.1.1 = false :=
  rfl

@[simp] theorem literalRightSeamClosedReceiverRoot_anchor
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (incoming blockInput : In₁ × In₂) :
    (package.literalRightSeamClosedReceiverRoot A strategy hwin state incoming
      blockInput).2.2.1.1 = true :=
  rfl

/-- The branch roots share precisely the fresh occurrence key.  This does not
identify their row or their member anchor. -/
theorem literalRightSeamReceiverBranchRoots_same_key
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (incoming blockInput : In₁ × In₂) :
    (package.literalRightSeamStrictOpenReceiverRoot A strategy hwin state
      incoming blockInput).1 =
      (package.literalRightSeamClosedReceiverRoot A strategy hwin state
        incoming blockInput).1 :=
  rfl

/-- In particular the two semantic poststates have not been collapsed: their
row tags already separate them. -/
theorem literalRightSeamReceiverBranchRoots_ne
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (incoming blockInput : In₁ × In₂) :
    package.literalRightSeamStrictOpenReceiverRoot A strategy hwin state
        incoming blockInput ≠
      package.literalRightSeamClosedReceiverRoot A strategy hwin state incoming
        blockInput := by
  intro heq
  have hrow := congrArg
    (fun receiver : RightReceiver A strategy hwin package ↦ receiver.2.1) heq
  cases hrow

/-! ## The current output is selected from the old tables -/

/-- Current receive paired with the fresh strict-open poststate.  The two old
member anchors are explicit because resolving the previous fork is logically
independent of creating this fresh branch. -/
noncomputable def successorLiteralCrossStrictOpenReceive
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (incoming blockInput : In₁ × In₂)
    (oldRightAnchor oldLeftAnchor : Bool) :
    (Out₁ × Out₂) × RightReceiver A strategy hwin package :=
  (package.successorLiteralCrossSelectedReceiveOutputs A strategy hwin state
      incoming blockInput oldRightAnchor oldLeftAnchor,
    package.literalRightSeamStrictOpenReceiverRoot A strategy hwin state
      incoming blockInput)

/-- Current receive paired with the fresh closed poststate. -/
noncomputable def successorLiteralCrossClosedReceive
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (incoming blockInput : In₁ × In₂)
    (oldRightAnchor oldLeftAnchor : Bool) :
    (Out₁ × Out₂) × RightReceiver A strategy hwin package :=
  (package.successorLiteralCrossSelectedReceiveOutputs A strategy hwin state
      incoming blockInput oldRightAnchor oldLeftAnchor,
    package.literalRightSeamClosedReceiverRoot A strategy hwin state incoming
      blockInput)

/-- In the strict-open branch, the currently emitted physical pair is the two
coordinates of the one guarded successor cut.  The fresh root occurs only in
the poststate coordinate. -/
theorem successorLiteralCrossStrictOpenReceive_output_eq_nextPairCut
    (package : Package A strategy hwin initial)
    {state : State A strategy hwin (initial := initial)}
    (hreachable :
      ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
        initial (CrossValid A strategy hwin) package.policy state)
    (incoming blockInput : In₁ × In₂)
    (oldRightAnchor oldLeftAnchor : Bool) :
    (package.successorLiteralCrossStrictOpenReceive A strategy hwin state
      incoming blockInput oldRightAnchor oldLeftAnchor).1 =
      (((package.nextPairAt A strategy hwin state incoming).rightRootRecord A
          strategy hwin blockInput).2.1.physical.closingBoth,
        ((package.nextPairAt A strategy hwin state incoming).leftRootRecord A
          strategy hwin blockInput).2.1.physical.closingBoth) := by
  exact package.successorLiteralCrossSelectedReceiveOutputs_eq_nextPairCut A
    strategy hwin hreachable incoming blockInput oldRightAnchor oldLeftAnchor

/-- The closed branch emits the same coherent current cut, while retaining
the distinct `.both`/true fresh poststate. -/
theorem successorLiteralCrossClosedReceive_output_eq_nextPairCut
    (package : Package A strategy hwin initial)
    {state : State A strategy hwin (initial := initial)}
    (hreachable :
      ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
        initial (CrossValid A strategy hwin) package.policy state)
    (incoming blockInput : In₁ × In₂)
    (oldRightAnchor oldLeftAnchor : Bool) :
    (package.successorLiteralCrossClosedReceive A strategy hwin state incoming
      blockInput oldRightAnchor oldLeftAnchor).1 =
      (((package.nextPairAt A strategy hwin state incoming).rightRootRecord A
          strategy hwin blockInput).2.1.physical.closingBoth,
        ((package.nextPairAt A strategy hwin state incoming).leftRootRecord A
          strategy hwin blockInput).2.1.physical.closingBoth) := by
  exact package.successorLiteralCrossSelectedReceiveOutputs_eq_nextPairCut A
    strategy hwin hreachable incoming blockInput oldRightAnchor oldLeftAnchor

/-- The current physical output cannot reveal which fresh poststate is being
stored.  This equality follows through the common successor cut, not by
identifying the poststates. -/
theorem successorLiteralCrossReceiverBranches_output_eq
    (package : Package A strategy hwin initial)
    {state : State A strategy hwin (initial := initial)}
    (hreachable :
      ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
        initial (CrossValid A strategy hwin) package.policy state)
    (incoming blockInput : In₁ × In₂)
    (strictOldRightAnchor strictOldLeftAnchor : Bool)
    (closedOldRightAnchor closedOldLeftAnchor : Bool) :
    (package.successorLiteralCrossStrictOpenReceive A strategy hwin state
        incoming blockInput strictOldRightAnchor strictOldLeftAnchor).1 =
      (package.successorLiteralCrossClosedReceive A strategy hwin state
        incoming blockInput closedOldRightAnchor closedOldLeftAnchor).1 := by
  rw [package.successorLiteralCrossStrictOpenReceive_output_eq_nextPairCut A
      strategy hwin hreachable incoming blockInput strictOldRightAnchor
      strictOldLeftAnchor,
    package.successorLiteralCrossClosedReceive_output_eq_nextPairCut A strategy
      hwin hreachable incoming blockInput closedOldRightAnchor
      closedOldLeftAnchor]

/-! ## Exact false/true pending equations for generic re-encapsulation -/

/-- The concrete fresh right fork's open candidate is literally the false
member at the shared table root with empty retained-stage payload. -/
@[simp] theorem successorLiteralCrossFreshRightPending_open
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (incoming blockInput : In₁ × In₂) :
    let key := package.successorLiteralCrossFreshSeamKey A strategy hwin state
      incoming blockInput
    (package.literalRightSeamFreshPendingSenderFork A strategy hwin key
      ).openControl =
      ((⟨key, false,
          (package.literalRightSeamStagedSenderInitial A strategy hwin key).2⟩,
        none) : RightPending A strategy hwin package) :=
  rfl

/-- The closed candidate is the true member at the identical table root and
payload. -/
@[simp] theorem successorLiteralCrossFreshRightPending_closed
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (incoming blockInput : In₁ × In₂) :
    let key := package.successorLiteralCrossFreshSeamKey A strategy hwin state
      incoming blockInput
    (package.literalRightSeamFreshPendingSenderFork A strategy hwin key
      ).closedControl =
      ((⟨key, true,
          (package.literalRightSeamStagedSenderInitial A strategy hwin key).2⟩,
        none) : RightPending A strategy hwin package) :=
  rfl

/-- Generic open shape required by `DeferredFreshReceiveLaws.one` or `.two`,
depending on which endpoint owns the right-seam sender in the joint carrier. -/
@[simp] theorem successorLiteralCrossFreshRightPending_repacked_open
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (incoming blockInput : In₁ × In₂) :
    let key := package.successorLiteralCrossFreshSeamKey A strategy hwin state
      incoming blockInput
    package.literalRightSeamPendingEquiv A strategy hwin
        (package.literalRightSeamFreshPendingSenderFork A strategy hwin key
          ).openControl =
      ((false,
        package.literalRightSeamStagedSenderInitial A strategy hwin key,
        none) :
        FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
          (RightShared A strategy hwin package)
          (Option (RightStage A strategy hwin package))) :=
  rfl

/-- Matching generic closed shape with the same shared control and payload. -/
@[simp] theorem successorLiteralCrossFreshRightPending_repacked_closed
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (incoming blockInput : In₁ × In₂) :
    let key := package.successorLiteralCrossFreshSeamKey A strategy hwin state
      incoming blockInput
    package.literalRightSeamPendingEquiv A strategy hwin
        (package.literalRightSeamFreshPendingSenderFork A strategy hwin key
          ).closedControl =
      ((true,
        package.literalRightSeamStagedSenderInitial A strategy hwin key,
        none) :
        FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
          (RightShared A strategy hwin package)
          (Option (RightStage A strategy hwin package))) :=
  rfl

/-- Pair form: repacking the concrete exact fork is the generic canonical
false/true fork. -/
theorem successorLiteralCrossFreshRightPending_repacked_fork
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (incoming blockInput : In₁ × In₂) :
    let key := package.successorLiteralCrossFreshSeamKey A strategy hwin state
      incoming blockInput
    let concrete := package.literalRightSeamFreshPendingSenderFork A strategy
      hwin key
    FiniteDelayedFork.mk
        (package.literalRightSeamPendingEquiv A strategy hwin
          concrete.openControl)
        (package.literalRightSeamPendingEquiv A strategy hwin
          concrete.closedControl) =
      FiniteAcknowledgedDelayedCarrier.deferredMemberFork
        (package.literalRightSeamStagedSenderInitial A strategy hwin key)
        (none : Option (RightStage A strategy hwin package)) :=
  rfl

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
