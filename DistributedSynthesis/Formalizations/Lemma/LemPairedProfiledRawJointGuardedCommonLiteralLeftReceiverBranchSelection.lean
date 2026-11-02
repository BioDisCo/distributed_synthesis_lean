/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralRightReceiverBranchSelection
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralDeferredMemberAdapters

/-!
# Left-seam receive branch selection

This is the exact mirror of the right-seam branch API.  `PairedEntryRow` is
orientation-relative and has constructors `first` and `both`: consequently a
strict-left occurrence is the mirror table's `first` row, not a nonexistent
`second` row.  Its member is `false`; the simultaneous closed occurrence is
row `both` with member `true`.

The two fresh roots share one occurrence-specific key but remain distinct.
The physical output emitted in the current round still comes from the old
selected literal-cross tables and is the one `nextPairAt` cut for arbitrary
old member choices.  The fresh left pending fork is also exposed after the
generic dependent-key repacking: its candidates are literally
`(false, shared, none)` and `(true, shared, none)`.  These are the exact
witness equations consumed by `DeferredFreshReceiveLaws`.

No runtime map receives a graph, orientation, leader bit, history, or view.
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

private abbrev LeftReceiver
    (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralLeftSeamStagedReceiverState A strategy
    hwin package

private abbrev LeftPending
    (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralLeftSeamDeferredSenderCandidate A
    strategy hwin package

private abbrev LeftShared
    (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralLeftSeamStagedSenderState A strategy hwin
    package

private abbrev LeftStage
    (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralLeftSeamStage A strategy hwin package

/-! ## The two distinct fresh mirror roots -/

/-- Fresh poststate for a strict-left occurrence.  `first` names the strict
row in each orientation-specific paired-entry object. -/
noncomputable def literalLeftSeamStrictOpenReceiverRoot
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (incoming blockInput : In₁ × In₂) : LeftReceiver A strategy hwin package :=
  package.literalLeftSeamStagedReceiverInitial A strategy hwin
    (package.successorLiteralCrossFreshSeamKey A strategy hwin state incoming
      blockInput) .first false

/-- Fresh poststate for the simultaneous mirror interpretation. -/
noncomputable def literalLeftSeamClosedReceiverRoot
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (incoming blockInput : In₁ × In₂) : LeftReceiver A strategy hwin package :=
  package.literalLeftSeamStagedReceiverInitial A strategy hwin
    (package.successorLiteralCrossFreshSeamKey A strategy hwin state incoming
      blockInput) .both true

@[simp] theorem literalLeftSeamStrictOpenReceiverRoot_key
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (incoming blockInput : In₁ × In₂) :
    (package.literalLeftSeamStrictOpenReceiverRoot A strategy hwin state
      incoming blockInput).1 =
      package.successorLiteralCrossFreshSeamKey A strategy hwin state incoming
        blockInput :=
  rfl

@[simp] theorem literalLeftSeamClosedReceiverRoot_key
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (incoming blockInput : In₁ × In₂) :
    (package.literalLeftSeamClosedReceiverRoot A strategy hwin state incoming
      blockInput).1 =
      package.successorLiteralCrossFreshSeamKey A strategy hwin state incoming
        blockInput :=
  rfl

@[simp] theorem literalLeftSeamStrictOpenReceiverRoot_row
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (incoming blockInput : In₁ × In₂) :
    (package.literalLeftSeamStrictOpenReceiverRoot A strategy hwin state
      incoming blockInput).2.1 = .first :=
  rfl

@[simp] theorem literalLeftSeamClosedReceiverRoot_row
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (incoming blockInput : In₁ × In₂) :
    (package.literalLeftSeamClosedReceiverRoot A strategy hwin state incoming
      blockInput).2.1 = .both :=
  rfl

@[simp] theorem literalLeftSeamStrictOpenReceiverRoot_anchor
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (incoming blockInput : In₁ × In₂) :
    (package.literalLeftSeamStrictOpenReceiverRoot A strategy hwin state
      incoming blockInput).2.2.1.1 = false :=
  rfl

@[simp] theorem literalLeftSeamClosedReceiverRoot_anchor
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (incoming blockInput : In₁ × In₂) :
    (package.literalLeftSeamClosedReceiverRoot A strategy hwin state incoming
      blockInput).2.2.1.1 = true :=
  rfl

theorem literalLeftSeamReceiverBranchRoots_same_key
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (incoming blockInput : In₁ × In₂) :
    (package.literalLeftSeamStrictOpenReceiverRoot A strategy hwin state
      incoming blockInput).1 =
      (package.literalLeftSeamClosedReceiverRoot A strategy hwin state incoming
        blockInput).1 :=
  rfl

/-- Same occurrence does not mean same semantic branch: the row tags separate
the roots before even inspecting their anchors. -/
theorem literalLeftSeamReceiverBranchRoots_ne
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (incoming blockInput : In₁ × In₂) :
    package.literalLeftSeamStrictOpenReceiverRoot A strategy hwin state
        incoming blockInput ≠
      package.literalLeftSeamClosedReceiverRoot A strategy hwin state incoming
        blockInput := by
  intro heq
  have hrow := congrArg
    (fun receiver : LeftReceiver A strategy hwin package ↦ receiver.2.1) heq
  cases hrow

/-! ## Current old-table output at the same occurrence -/

noncomputable def successorLiteralCrossLeftStrictOpenReceive
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (incoming blockInput : In₁ × In₂)
    (oldRightAnchor oldLeftAnchor : Bool) :
    (Out₁ × Out₂) × LeftReceiver A strategy hwin package :=
  (package.successorLiteralCrossSelectedReceiveOutputs A strategy hwin state
      incoming blockInput oldRightAnchor oldLeftAnchor,
    package.literalLeftSeamStrictOpenReceiverRoot A strategy hwin state
      incoming blockInput)

noncomputable def successorLiteralCrossLeftClosedReceive
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (incoming blockInput : In₁ × In₂)
    (oldRightAnchor oldLeftAnchor : Bool) :
    (Out₁ × Out₂) × LeftReceiver A strategy hwin package :=
  (package.successorLiteralCrossSelectedReceiveOutputs A strategy hwin state
      incoming blockInput oldRightAnchor oldLeftAnchor,
    package.literalLeftSeamClosedReceiverRoot A strategy hwin state incoming
      blockInput)

theorem successorLiteralCrossLeftStrictOpenReceive_output_eq_nextPairCut
    (package : Package A strategy hwin initial)
    {state : State A strategy hwin (initial := initial)}
    (hreachable :
      ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
        initial (CrossValid A strategy hwin) package.policy state)
    (incoming blockInput : In₁ × In₂)
    (oldRightAnchor oldLeftAnchor : Bool) :
    (package.successorLiteralCrossLeftStrictOpenReceive A strategy hwin state
      incoming blockInput oldRightAnchor oldLeftAnchor).1 =
      (((package.nextPairAt A strategy hwin state incoming).rightRootRecord A
          strategy hwin blockInput).2.1.physical.closingBoth,
        ((package.nextPairAt A strategy hwin state incoming).leftRootRecord A
          strategy hwin blockInput).2.1.physical.closingBoth) := by
  exact package.successorLiteralCrossSelectedReceiveOutputs_eq_nextPairCut A
    strategy hwin hreachable incoming blockInput oldRightAnchor oldLeftAnchor

theorem successorLiteralCrossLeftClosedReceive_output_eq_nextPairCut
    (package : Package A strategy hwin initial)
    {state : State A strategy hwin (initial := initial)}
    (hreachable :
      ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
        initial (CrossValid A strategy hwin) package.policy state)
    (incoming blockInput : In₁ × In₂)
    (oldRightAnchor oldLeftAnchor : Bool) :
    (package.successorLiteralCrossLeftClosedReceive A strategy hwin state
      incoming blockInput oldRightAnchor oldLeftAnchor).1 =
      (((package.nextPairAt A strategy hwin state incoming).rightRootRecord A
          strategy hwin blockInput).2.1.physical.closingBoth,
        ((package.nextPairAt A strategy hwin state incoming).leftRootRecord A
          strategy hwin blockInput).2.1.physical.closingBoth) := by
  exact package.successorLiteralCrossSelectedReceiveOutputs_eq_nextPairCut A
    strategy hwin hreachable incoming blockInput oldRightAnchor oldLeftAnchor

theorem successorLiteralCrossLeftReceiverBranches_output_eq
    (package : Package A strategy hwin initial)
    {state : State A strategy hwin (initial := initial)}
    (hreachable :
      ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
        initial (CrossValid A strategy hwin) package.policy state)
    (incoming blockInput : In₁ × In₂)
    (strictOldRightAnchor strictOldLeftAnchor : Bool)
    (closedOldRightAnchor closedOldLeftAnchor : Bool) :
    (package.successorLiteralCrossLeftStrictOpenReceive A strategy hwin state
        incoming blockInput strictOldRightAnchor strictOldLeftAnchor).1 =
      (package.successorLiteralCrossLeftClosedReceive A strategy hwin state
        incoming blockInput closedOldRightAnchor closedOldLeftAnchor).1 := by
  rw [package.successorLiteralCrossLeftStrictOpenReceive_output_eq_nextPairCut
      A strategy hwin hreachable incoming blockInput strictOldRightAnchor
      strictOldLeftAnchor,
    package.successorLiteralCrossLeftClosedReceive_output_eq_nextPairCut A
      strategy hwin hreachable incoming blockInput closedOldRightAnchor
      closedOldLeftAnchor]

/-! ## Exact false/true pending equations for generic re-encapsulation -/

/-- The concrete fresh mirror fork's open candidate is exactly the false
member at the shared table root with empty stage payload. -/
@[simp] theorem successorLiteralCrossFreshLeftPending_open
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (incoming blockInput : In₁ × In₂) :
    let key := package.successorLiteralCrossFreshSeamKey A strategy hwin state
      incoming blockInput
    (package.literalLeftSeamFreshDeferredSenderFork A strategy hwin key
      ).openControl =
      ((⟨key, false,
          (package.literalLeftSeamStagedSenderInitial A strategy hwin key).2⟩,
        none) : LeftPending A strategy hwin package) :=
  rfl

/-- Closed is the true member of that very same table root and payload. -/
@[simp] theorem successorLiteralCrossFreshLeftPending_closed
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (incoming blockInput : In₁ × In₂) :
    let key := package.successorLiteralCrossFreshSeamKey A strategy hwin state
      incoming blockInput
    (package.literalLeftSeamFreshDeferredSenderFork A strategy hwin key
      ).closedControl =
      ((⟨key, true,
          (package.literalLeftSeamStagedSenderInitial A strategy hwin key).2⟩,
        none) : LeftPending A strategy hwin package) :=
  rfl

/-- After the generic repacking, the false candidate has exactly the shape
required by the `openRecvTwo` equation of `DeferredFreshReceiveLaws`. -/
@[simp] theorem successorLiteralCrossFreshLeftPending_repacked_open
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (incoming blockInput : In₁ × In₂) :
    let key := package.successorLiteralCrossFreshSeamKey A strategy hwin state
      incoming blockInput
    package.literalLeftSeamDeferredEquiv A strategy hwin
        (package.literalLeftSeamFreshDeferredSenderFork A strategy hwin key
          ).openControl =
      ((false,
        package.literalLeftSeamStagedSenderInitial A strategy hwin key,
        none) :
        FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
          (LeftShared A strategy hwin package)
          (Option (LeftStage A strategy hwin package))) :=
  rfl

/-- The closed candidate is the matching true member with definitionally the
same shared state and payload. -/
@[simp] theorem successorLiteralCrossFreshLeftPending_repacked_closed
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (incoming blockInput : In₁ × In₂) :
    let key := package.successorLiteralCrossFreshSeamKey A strategy hwin state
      incoming blockInput
    package.literalLeftSeamDeferredEquiv A strategy hwin
        (package.literalLeftSeamFreshDeferredSenderFork A strategy hwin key
          ).closedControl =
      ((true,
        package.literalLeftSeamStagedSenderInitial A strategy hwin key,
        none) :
        FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
          (LeftShared A strategy hwin package)
          (Option (LeftStage A strategy hwin package))) :=
  rfl

/-- Pair form: the concrete fresh fork is exactly the generic canonical
false/true fork after dependent-key repacking. -/
theorem successorLiteralCrossFreshLeftPending_repacked_fork
    (package : Package A strategy hwin initial)
    (state : State A strategy hwin (initial := initial))
    (incoming blockInput : In₁ × In₂) :
    let key := package.successorLiteralCrossFreshSeamKey A strategy hwin state
      incoming blockInput
    let concrete := package.literalLeftSeamFreshDeferredSenderFork A strategy
      hwin key
    FiniteDelayedFork.mk
        (package.literalLeftSeamDeferredEquiv A strategy hwin
          concrete.openControl)
        (package.literalLeftSeamDeferredEquiv A strategy hwin
          concrete.closedControl) =
      FiniteAcknowledgedDelayedCarrier.deferredMemberFork
        (package.literalLeftSeamStagedSenderInitial A strategy hwin key)
        (none : Option (LeftStage A strategy hwin package)) :=
  rfl

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
