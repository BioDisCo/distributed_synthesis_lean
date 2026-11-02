/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteAcknowledgedExactClosingPhaseLiveOverlay
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankRetainedController

/-!
# Active/pending staging for the marked retained bank

The retained carrier runs one installed pair of literal tables while a
receive prepares the finite bank tag for the next installation.  Those are
different roles: replacing the only stored tag at the receive would make the
tag denote the child tables while the retained relay still denotes the
advanced parent tables.

This file isolates the smallest finite state which keeps the roles separate.
It instantiates the repository's `PhaseLiveShared` wrapper with

* an active finite bank tag and active endpoint control;
* a finite open/closed fork of pending bank tags; and
* the endpoint-local phase bit already used by the acknowledged carrier.

The outer acknowledged relay chooses the stored fork member.  No definition
here is passed a graph, orientation, hierarchy side, leader bit,
strict-leader bit, history, or view.

There are two possible promotion operations.  Restart promotion installs the
chosen child tag's canonical retained root and is unconditional.  Relay-
retaining promotion keeps the advanced parent relay and merely reinterprets
it under the child tag.  The final iff theorems identify exactly when that
reinterpretation is sound: the retained relay must equal the child's
canonical installed relay.  Thus later code cannot silently use universal
policy reachability as if it supplied same-occurrence relay equality.
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

private abbrev RetainedTag :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A strategy
    hwin

private abbrev RetainedOne :=
  ProfiledRawJointHybridLiteralPrefixRetainedOneControl A

private abbrev RetainedTwo :=
  ProfiledRawJointHybridLiteralPrefixRetainedTwoControl A

private abbrev PendingFork :=
  FiniteDelayedFork (RetainedTag A strategy hwin)

/-! ## The two finite staged controls -/

/-- Process one's active retained control and its unresolved next tag.  The
unit receiver fork is deliberately inert: all four live table controls are
already present in `RetainedOne`'s relay. -/
abbrev
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneStage :=
  FiniteAcknowledgedDelayedCarrier.PhaseLiveShared
    (RetainedTag A strategy hwin × RetainedOne A)
    (PendingFork A strategy hwin) PUnit.{1}

/-- Process-two mirror. -/
abbrev
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoStage :=
  FiniteAcknowledgedDelayedCarrier.PhaseLiveShared
    (RetainedTag A strategy hwin × RetainedTwo A)
    (PendingFork A strategy hwin) PUnit.{1}

private abbrev OneStage :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneStage A
    strategy hwin

private abbrev TwoStage :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoStage A
    strategy hwin

noncomputable instance
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneStageFintype :
    Fintype (OneStage A strategy hwin) := by
  classical
  infer_instance

noncomputable instance
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoStageFintype :
    Fintype (TwoStage A strategy hwin) := by
  classical
  infer_instance

/-- Build a process-one stage.  The two unit receiver interpretations make
the fact that the retained relay already contains every receiver explicit. -/
def profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneStageOf
    (activeTag : RetainedTag A strategy hwin) (active : RetainedOne A)
    (pending : PendingFork A strategy hwin) (phase : Bool) :
    OneStage A strategy hwin :=
  FiniteAcknowledgedDelayedCarrier.PhaseLiveShared.fresh
    (activeTag, active) pending phase PUnit.unit PUnit.unit

/-- Process-two constructor. -/
def profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoStageOf
    (activeTag : RetainedTag A strategy hwin) (active : RetainedTwo A)
    (pending : PendingFork A strategy hwin) (phase : Bool) :
    TwoStage A strategy hwin :=
  FiniteAcknowledgedDelayedCarrier.PhaseLiveShared.fresh
    (activeTag, active) pending phase PUnit.unit PUnit.unit

/-- A resolved tag represented as the canonical open/closed fork. -/
def profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTagFork
    (tag : RetainedTag A strategy hwin) : PendingFork A strategy hwin :=
  ⟨tag, tag⟩

/-- Canonical aligned process-one stage at one installed tag. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneStageInitial
    (tag : RetainedTag A strategy hwin) (phase : Bool) :
    OneStage A strategy hwin :=
  profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneStageOf A
    strategy hwin tag
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedInstallOne A
      strategy hwin tag).2
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTagFork A
      strategy hwin tag) phase

/-- Process-two mirror. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoStageInitial
    (tag : RetainedTag A strategy hwin) (phase : Bool) :
    TwoStage A strategy hwin :=
  profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoStageOf A
    strategy hwin tag
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedInstallTwo A
      strategy hwin tag).2
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTagFork A
      strategy hwin tag) phase

/-! ## Transparent projections -/

def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneStage.activeTag
    (state : OneStage A strategy hwin) : RetainedTag A strategy hwin :=
  state.baseShared.1

def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneStage.activeControl
    (state : OneStage A strategy hwin) : RetainedOne A :=
  state.baseShared.2

def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneStage.pendingTag
    (state : OneStage A strategy hwin) (member : Bool) :
    RetainedTag A strategy hwin :=
  state.basePayload.candidate member

def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoStage.activeTag
    (state : TwoStage A strategy hwin) : RetainedTag A strategy hwin :=
  state.baseShared.1

def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoStage.activeControl
    (state : TwoStage A strategy hwin) : RetainedTwo A :=
  state.baseShared.2

def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoStage.pendingTag
    (state : TwoStage A strategy hwin) (member : Bool) :
    RetainedTag A strategy hwin :=
  state.basePayload.candidate member

/-! ## Unconditional restart promotion -/

/-- Select one acknowledged pending member and install its process-one root.
The pending fork is reset to the resolved diagonal. -/
noncomputable def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneStage.promoteRestart
    (state : OneStage A strategy hwin) (member : Bool) :
    OneStage A strategy hwin :=
  let tag := state.pendingTag A strategy hwin member
  profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneStageInitial
    A strategy hwin tag state.localPhase

/-- Process-two mirror. -/
noncomputable def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoStage.promoteRestart
    (state : TwoStage A strategy hwin) (member : Bool) :
    TwoStage A strategy hwin :=
  let tag := state.pendingTag A strategy hwin member
  profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoStageInitial
    A strategy hwin tag state.localPhase

@[simp] theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneStage.promoteRestart_activeTag
    (state : OneStage A strategy hwin) (member : Bool) :
    (state.promoteRestart A strategy hwin member).activeTag A strategy hwin =
      state.pendingTag A strategy hwin member :=
  rfl

@[simp] theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoStage.promoteRestart_activeTag
    (state : TwoStage A strategy hwin) (member : Bool) :
    (state.promoteRestart A strategy hwin member).activeTag A strategy hwin =
      state.pendingTag A strategy hwin member :=
  rfl

@[simp] theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneStage.promoteRestart_activeControl
    (state : OneStage A strategy hwin) (member : Bool) :
    (state.promoteRestart A strategy hwin member).activeControl A strategy hwin =
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedInstallOne
        A strategy hwin (state.pendingTag A strategy hwin member)).2 :=
  rfl

@[simp] theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoStage.promoteRestart_activeControl
    (state : TwoStage A strategy hwin) (member : Bool) :
    (state.promoteRestart A strategy hwin member).activeControl A strategy hwin =
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedInstallTwo
        A strategy hwin (state.pendingTag A strategy hwin member)).2 :=
  rfl

/-! ## The exact retain-versus-restart gate -/

/-- Reset the observable output and local receive bit to the child root while
retaining process one's advanced parent relay. -/
def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedReinterpretOne
    (tag : RetainedTag A strategy hwin) (old : RetainedOne A) : RetainedOne A :=
  let fresh :=
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedInstallOne A
      strategy hwin tag).2
  (fresh.1, (fresh.2.1, old.2.2))

/-- Process-two mirror. -/
def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedReinterpretTwo
    (tag : RetainedTag A strategy hwin) (old : RetainedTwo A) : RetainedTwo A :=
  let fresh :=
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedInstallTwo A
      strategy hwin tag).2
  (fresh.1, (fresh.2.1, old.2.2))

/-- Exact model obligation for reusing process one's advanced relay at the
chosen child instead of restarting it. -/
def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneStage.RelayReinterpretable
    (state : OneStage A strategy hwin) (member : Bool) : Prop :=
  state.activeControl A strategy hwin |>.2.2 =
    ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedInstallOne
      A strategy hwin (state.pendingTag A strategy hwin member)).2).2.2

/-- Process-two mirror. -/
def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoStage.RelayReinterpretable
    (state : TwoStage A strategy hwin) (member : Bool) : Prop :=
  state.activeControl A strategy hwin |>.2.2 =
    ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedInstallTwo
      A strategy hwin (state.pendingTag A strategy hwin member)).2).2.2

/-- Promotion which keeps the old relay.  It is executable finite data, but
the theorem below prevents treating it as a child installation without the
explicit relay equation. -/
def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneStage.promoteRetainingRelay
    (state : OneStage A strategy hwin) (member : Bool) :
    OneStage A strategy hwin :=
  let tag := state.pendingTag A strategy hwin member
  profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneStageOf A
    strategy hwin tag
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedReinterpretOne
      A strategy hwin tag (state.activeControl A strategy hwin))
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTagFork A
      strategy hwin tag) state.localPhase

/-- Process-two mirror. -/
def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoStage.promoteRetainingRelay
    (state : TwoStage A strategy hwin) (member : Bool) :
    TwoStage A strategy hwin :=
  let tag := state.pendingTag A strategy hwin member
  profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoStageOf A
    strategy hwin tag
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedReinterpretTwo
      A strategy hwin tag (state.activeControl A strategy hwin))
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTagFork A
      strategy hwin tag) state.localPhase

/-- Retaining process one's relay is extensionally the same as an honest
child restart exactly under `RelayReinterpretable`. -/
theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneStage.promoteRetainingRelay_activeControl_eq_restart_iff
    (state : OneStage A strategy hwin) (member : Bool) :
    (state.promoteRetainingRelay A strategy hwin member).activeControl A
          strategy hwin =
        (state.promoteRestart A strategy hwin member).activeControl A strategy
          hwin ↔
      state.RelayReinterpretable A strategy hwin member := by
  simp [ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneStage.promoteRetainingRelay,
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneStage.promoteRestart,
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneStage.activeControl,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedReinterpretOne,
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneStage.RelayReinterpretable,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneStageOf,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneStageInitial,
    FiniteAcknowledgedDelayedCarrier.PhaseLiveShared.fresh]
  constructor
  · intro h
    exact congrArg (fun control ↦ control.2.2) h
  · intro h
    exact Prod.ext rfl (Prod.ext rfl h)

/-- Process-two mirror. -/
theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoStage.promoteRetainingRelay_activeControl_eq_restart_iff
    (state : TwoStage A strategy hwin) (member : Bool) :
    (state.promoteRetainingRelay A strategy hwin member).activeControl A
          strategy hwin =
        (state.promoteRestart A strategy hwin member).activeControl A strategy
          hwin ↔
      state.RelayReinterpretable A strategy hwin member := by
  simp [ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoStage.promoteRetainingRelay,
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoStage.promoteRestart,
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoStage.activeControl,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedReinterpretTwo,
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoStage.RelayReinterpretable,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoStageOf,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoStageInitial,
    FiniteAcknowledgedDelayedCarrier.PhaseLiveShared.fresh]
  constructor
  · intro h
    exact congrArg (fun control ↦ control.2.2) h
  · intro h
    exact Prod.ext rfl (Prod.ext rfl h)

/-! ## Paired promotion bookkeeping -/

/-- Equal pending forks give equal active tags after an acknowledged restart
promotion, independently of the old active tags and relays. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetained_promoteRestart_keys
    (one : OneStage A strategy hwin) (two : TwoStage A strategy hwin)
    (hpending : one.basePayload = two.basePayload) (member : Bool) :
    (one.promoteRestart A strategy hwin member).activeTag A strategy hwin =
      (two.promoteRestart A strategy hwin member).activeTag A strategy hwin := by
  change one.basePayload.candidate member = two.basePayload.candidate member
  rw [hpending]

/-- The canonical installed pair is recovered when both stages start from
one common tag. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetained_stageInitial_pair
    (tag : RetainedTag A strategy hwin) (phaseOne phaseTwo : Bool) :
    ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneStageInitial
          A strategy hwin tag phaseOne).activeControl A strategy hwin,
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoStageInitial
          A strategy hwin tag phaseTwo).activeControl A strategy hwin) =
      tag.initial A strategy hwin :=
  rfl

/-! ## Restart promotion and the exact blind pair test

Retaining the whole parent relay is stronger than the acknowledged carrier
needs.  Its unresolved open/closed fork may instead contain two honest child
restarts.  While an endpoint is blind, process one reads only the right
sender state and process two reads only the left sender state.  Equality of
that one relevant sender state is therefore a bisimulation at arbitrary blind
depth; the other retained receiver/table lanes may differ.
-/

/-- One blind process-one step through a staged active control.  Pending tags
and inactive receiver lanes are retained by the underlying retained carrier. -/
def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneStageNoRecv
    (blindPhase : Bool) (state : OneStage A strategy hwin) (input : In₁) :
    OneStage A strategy hwin × Out₁ :=
  let next :=
    profiledRawJointHybridLiteralPrefixRetainedNoRecvOne A
      (state.activeControl A strategy hwin) input
  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneStageOf A
      strategy hwin (state.activeTag A strategy hwin) next state.basePayload
      blindPhase,
    next.1)

/-- Process-two mirror. -/
def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoStageNoRecv
    (blindPhase : Bool) (state : TwoStage A strategy hwin) (input : In₂) :
    TwoStage A strategy hwin × Out₂ :=
  let next :=
    profiledRawJointHybridLiteralPrefixRetainedNoRecvTwo A
      (state.activeControl A strategy hwin) input
  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoStageOf A
      strategy hwin (state.activeTag A strategy hwin) next state.basePayload
      blindPhase,
    next.1)

/-- Process-one blind equivalence remembers exactly the live right-sender
state.  Tags, anchors, and both receiver states may differ. -/
def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneStage.Blind
    (left right : OneStage A strategy hwin) : Prop :=
  (left.activeControl A strategy hwin).2.2.1.1 =
    (right.activeControl A strategy hwin).2.2.1.1

/-- Process-two mirror: only the live left sender is observable while blind. -/
def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoStage.Blind
    (left right : TwoStage A strategy hwin) : Prop :=
  (left.activeControl A strategy hwin).2.2.2.1 =
    (right.activeControl A strategy hwin).2.2.2.1

/-- Equality of the live right sender gives equal output and remains true
after an arbitrary process-one blind input. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneStageBlind_noRecv
    (blindPhase : Bool) (left right : OneStage A strategy hwin)
    (input : In₁)
    (hblind : left.Blind A strategy hwin right) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneStageNoRecv
          A strategy hwin blindPhase left input).2 =
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneStageNoRecv
          A strategy hwin blindPhase right input).2 ∧
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneStageNoRecv
          A strategy hwin blindPhase left input).1.Blind A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneStageNoRecv
          A strategy hwin blindPhase right input).1 := by
  unfold ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneStage.Blind at hblind
  change left.baseShared.2.2.2.1.1 = right.baseShared.2.2.2.1.1 at hblind
  unfold ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneStage.Blind
  simp only [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneStageNoRecv,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneStageOf,
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneStage.activeControl,
    profiledRawJointHybridLiteralPrefixRetainedNoRecvOne,
    FiniteAcknowledgedDelayedCarrier.PhaseLiveShared.fresh]
  rw [hblind]
  exact ⟨rfl, rfl⟩

/-- Process-two blind preservation. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoStageBlind_noRecv
    (blindPhase : Bool) (left right : TwoStage A strategy hwin)
    (input : In₂)
    (hblind : left.Blind A strategy hwin right) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoStageNoRecv
          A strategy hwin blindPhase left input).2 =
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoStageNoRecv
          A strategy hwin blindPhase right input).2 ∧
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoStageNoRecv
          A strategy hwin blindPhase left input).1.Blind A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoStageNoRecv
          A strategy hwin blindPhase right input).1 := by
  unfold ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoStage.Blind at hblind
  change left.baseShared.2.2.2.2.1 = right.baseShared.2.2.2.2.1 at hblind
  unfold ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoStage.Blind
  simp only [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoStageNoRecv,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoStageOf,
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoStage.activeControl,
    profiledRawJointHybridLiteralPrefixRetainedNoRecvTwo,
    FiniteAcknowledgedDelayedCarrier.PhaseLiveShared.fresh]
  rw [hblind]
  exact ⟨rfl, rfl⟩

/-- The generic acknowledged-carrier no-receive law follows with no semantic
hypothesis once its fresh fork has equal live right-sender states. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneStageBlindNoRecvLaws
    (blindPhase : Bool) :
    FiniteAcknowledgedDelayedCarrier.BlindNoRecvLaws
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneStageNoRecv
        A strategy hwin blindPhase)
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoStageNoRecv
        A strategy hwin blindPhase)
      (ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneStage.Blind
        A strategy hwin)
      (ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoStage.Blind
        A strategy hwin) where
  one := profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneStageBlind_noRecv
    A strategy hwin blindPhase
  two := profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoStageBlind_noRecv
    A strategy hwin blindPhase

/-- Two canonical child restarts are process-one blind-related whenever their
installed right moves agree.  Anchor bits and the left moves are irrelevant. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneStageInitial_blind_of_rightMove_eq
    (left right : RetainedTag A strategy hwin) (leftPhase rightPhase : Bool)
    (hmove : left.1.rightMove A strategy hwin =
      right.1.rightMove A strategy hwin) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneStageInitial
        A strategy hwin left leftPhase).Blind A strategy hwin
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneStageInitial
        A strategy hwin right rightPhase) := by
  unfold ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneStage.Blind
  simp only [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneStageInitial,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneStageOf,
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneStage.activeControl,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedInstallOne,
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag.initial,
    profiledRawJointHybridLiteralPrefixRetainedInitial,
    profiledRawJointHybridLiteralPrefixRetainedRelayInitial,
    FiniteAcknowledgedDelayedCarrier.PhaseLiveShared.fresh]
  rw [hmove]

/-- Process-two mirror. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoStageInitial_blind_of_leftMove_eq
    (left right : RetainedTag A strategy hwin) (leftPhase rightPhase : Bool)
    (hmove : left.1.leftMove A strategy hwin =
      right.1.leftMove A strategy hwin) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoStageInitial
        A strategy hwin left leftPhase).Blind A strategy hwin
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoStageInitial
        A strategy hwin right rightPhase) := by
  unfold ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoStage.Blind
  simp only [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoStageInitial,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoStageOf,
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoStage.activeControl,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedInstallTwo,
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag.initial,
    profiledRawJointHybridLiteralPrefixRetainedInitial,
    profiledRawJointHybridLiteralPrefixRetainedRelayInitial,
    FiniteAcknowledgedDelayedCarrier.PhaseLiveShared.fresh]
  rw [hmove]

/-- Hence the process-one restart fork passes the dangerous blind-output test
as soon as the finite resolver supplies the same right move in both modes. -/
theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneStage.promoteRestart_blind_of_rightMove_eq
    (left right : OneStage A strategy hwin) (leftMember rightMember : Bool)
    (hmove :
      (left.pendingTag A strategy hwin leftMember).1.rightMove A strategy hwin =
        (right.pendingTag A strategy hwin rightMember).1.rightMove A strategy
          hwin) :
    (left.promoteRestart A strategy hwin leftMember).Blind A strategy hwin
      (right.promoteRestart A strategy hwin rightMember) := by
  exact
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneStageInitial_blind_of_rightMove_eq
      A strategy hwin _ _ left.localPhase right.localPhase hmove

/-- Process-two restart-fork test. -/
theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoStage.promoteRestart_blind_of_leftMove_eq
    (left right : TwoStage A strategy hwin) (leftMember rightMember : Bool)
    (hmove :
      (left.pendingTag A strategy hwin leftMember).1.leftMove A strategy hwin =
        (right.pendingTag A strategy hwin rightMember).1.leftMove A strategy
          hwin) :
    (left.promoteRestart A strategy hwin leftMember).Blind A strategy hwin
      (right.promoteRestart A strategy hwin rightMember) := by
  exact
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoStageInitial_blind_of_leftMove_eq
      A strategy hwin _ _ left.localPhase right.localPhase hmove

/-! ## Mode-aware restart forks

The acknowledgement carrier stores both meanings of a locally ambiguous
receive.  The two members below are honest restarts: no relay is silently
reinterpreted under a different bank tag.  The executable no-receive map then
advances both members.  Its output is sound precisely when the members agree
on the sender that is live at that endpoint; this is the small pair test that
the same-parent linked annotation has to discharge.
-/

/-- The two honest process-one restart interpretations of one ambiguous
receive.  `false` is the strict/open member and `true` is the
simultaneous/closed member. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneRestartFork
    (openTag closedTag : RetainedTag A strategy hwin) (phase : Bool) :
    FiniteDelayedFork (OneStage A strategy hwin) :=
  ⟨profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneStageInitial
      A strategy hwin openTag phase,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneStageInitial
      A strategy hwin closedTag phase⟩

/-- Process-two mirror. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoRestartFork
    (openTag closedTag : RetainedTag A strategy hwin) (phase : Bool) :
    FiniteDelayedFork (TwoStage A strategy hwin) :=
  ⟨profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoStageInitial
      A strategy hwin openTag phase,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoStageInitial
      A strategy hwin closedTag phase⟩

/-- A process-one fork is blind-coherent when its two graph interpretations
have the same live right-sender state. -/
def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneRestartForkBlind
    (fork : FiniteDelayedFork (OneStage A strategy hwin)) : Prop :=
  fork.openControl.Blind A strategy hwin fork.closedControl

/-- Process-two mirror. -/
def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoRestartForkBlind
    (fork : FiniteDelayedFork (TwoStage A strategy hwin)) : Prop :=
  fork.openControl.Blind A strategy hwin fork.closedControl

/-- Same-live-move tags produce a valid process-one ambiguity fork. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneRestartFork_blind_of_rightMove_eq
    (openTag closedTag : RetainedTag A strategy hwin) (phase : Bool)
    (hmove : openTag.1.rightMove A strategy hwin =
      closedTag.1.rightMove A strategy hwin) :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneRestartForkBlind
      A strategy hwin
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneRestartFork
        A strategy hwin openTag closedTag phase) := by
  exact
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneStageInitial_blind_of_rightMove_eq
      A strategy hwin openTag closedTag phase phase hmove

/-- Process-two same-live-move fork. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoRestartFork_blind_of_leftMove_eq
    (openTag closedTag : RetainedTag A strategy hwin) (phase : Bool)
    (hmove : openTag.1.leftMove A strategy hwin =
      closedTag.1.leftMove A strategy hwin) :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoRestartForkBlind
      A strategy hwin
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoRestartFork
        A strategy hwin openTag closedTag phase) := by
  exact
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoStageInitial_blind_of_leftMove_eq
      A strategy hwin openTag closedTag phase phase hmove

/-- In the important same-child case, the open/closed interpretations may
carry different finite anchor bits but are unconditionally process-one
blind-related. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneRestartFork_blind_of_same_child
    (child : ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl A
      strategy hwin)
    (openAnchors closedAnchors : Bool × Bool) (phase : Bool) :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneRestartForkBlind
      A strategy hwin
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneRestartFork
        A strategy hwin (child, openAnchors) (child, closedAnchors) phase) := by
  apply
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneRestartFork_blind_of_rightMove_eq
  rfl

/-- Process-two same-child mirror. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoRestartFork_blind_of_same_child
    (child : ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl A
      strategy hwin)
    (openAnchors closedAnchors : Bool × Bool) (phase : Bool) :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoRestartForkBlind
      A strategy hwin
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoRestartFork
        A strategy hwin (child, openAnchors) (child, closedAnchors) phase) := by
  apply
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoRestartFork_blind_of_leftMove_eq
  rfl

/-- Blind coherence is exactly sufficient for the acknowledged carrier to
emit a member-independent process-one output on the next no-receive. -/
theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneRestartForkBlind.noRecv_outputCoherent
    (blindPhase : Bool) (fork : FiniteDelayedFork (OneStage A strategy hwin))
    (hblind :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneRestartForkBlind
        A strategy hwin fork)
    (input : In₁) :
    fork.NoRecvMealyOutputCoherent
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneStageNoRecv
        A strategy hwin blindPhase) input := by
  exact
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneStageBlind_noRecv
      A strategy hwin blindPhase fork.openControl fork.closedControl input
        hblind).1

/-- The branchwise no-receive update preserves process-one fork coherence. -/
theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneRestartForkBlind.noRecv
    (blindPhase : Bool) (fork : FiniteDelayedFork (OneStage A strategy hwin))
    (hblind :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneRestartForkBlind
        A strategy hwin fork)
    (input : In₁) :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneRestartForkBlind
      A strategy hwin
      (fork.noRecvMealy
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneStageNoRecv
          A strategy hwin blindPhase) input).1 := by
  exact
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneStageBlind_noRecv
      A strategy hwin blindPhase fork.openControl fork.closedControl input
        hblind).2

/-- Process-two member-independent blind output. -/
theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoRestartForkBlind.noRecv_outputCoherent
    (blindPhase : Bool) (fork : FiniteDelayedFork (TwoStage A strategy hwin))
    (hblind :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoRestartForkBlind
        A strategy hwin fork)
    (input : In₂) :
    fork.NoRecvMealyOutputCoherent
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoStageNoRecv
        A strategy hwin blindPhase) input := by
  exact
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoStageBlind_noRecv
      A strategy hwin blindPhase fork.openControl fork.closedControl input
        hblind).1

/-- Process-two branchwise preservation. -/
theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoRestartForkBlind.noRecv
    (blindPhase : Bool) (fork : FiniteDelayedFork (TwoStage A strategy hwin))
    (hblind :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoRestartForkBlind
        A strategy hwin fork)
    (input : In₂) :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoRestartForkBlind
      A strategy hwin
      (fork.noRecvMealy
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoStageNoRecv
          A strategy hwin blindPhase) input).1 := by
  exact
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoStageBlind_noRecv
      A strategy hwin blindPhase fork.openControl fork.closedControl input
        hblind).2

end

end DetParityAutomaton

end DistributedSynthesis
