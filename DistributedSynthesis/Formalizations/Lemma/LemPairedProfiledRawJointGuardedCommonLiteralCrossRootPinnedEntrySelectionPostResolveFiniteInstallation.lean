/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteCrossAnchorLocalCarrier
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionPostResolveJointTable

/-!
# Installing the joint post-resolve table at the resolving receive

The old entry-selection construction retained two unrelated payloads after a
resolving receive: a dormant strict seed and a live common owner.  The joint
table constructed in the preceding file is the replacement runtime payload.
This file checks the timing-sensitive part of that replacement.

First, the strict seed selected by the concrete resolving receive has exactly
the code of the root-pinned literal child used to construct the joint table.
Thus the new table is installed at that receive, rather than selected later
from output compatibility.  Second, both endpoints store the same finite move
and start from the same shared table control.  The blind endpoint carries no
strict/common bit.  The informed endpoint stores `false` for the strict child
and `true` for the simultaneous child, and every subsequent paired block step
preserves equality of the two table controls without restarting either
member.
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

/-! ## The concrete receive selects the installed strict child -/

/-- The strict-left seed retained by the old process-one receive and the
strict member of the new process-one joint table refer to the same literal
child code.  The equality is independent of the bootstrap member. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictLeftSeedAt_child_code
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) :
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictLeftSeedAt A
      strategy hwin initial entry input member).child.1 =
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictLeftLiteralChildAt
        A strategy initial entry input).code A := by
  let seed :=
    profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictLeftSeedAt A
      strategy hwin initial entry input member
  calc
    seed.child.1 =
        let one :=
          profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOneInitial A
            strategy hwin initial entry member
        (profiledRawJointGuardedCommonLeftLiteralCrossReceiverRecv A
          (one.2.2.candidate one.1) input.1 input.2).1.target .both :=
      seed.target_eq
    _ =
        (profiledRawJointHybridExactLeftUniformActivation A strategy hwin
          (profiledRawJointGuardedCommonPointInstalled A strategy initial)
          ).target .both [entry] input :=
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryInitial_strictLeft_target
        A strategy hwin initial entry input member
    _ =
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictLeftLiteralChildAt
          A strategy initial entry input).code A := by
      symm
      exact
        profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictLeftLiteralChildAt_code
          A strategy hwin initial entry input

/-- Process-two mirror: its concrete strict-right seed has exactly the child
code installed in the strict member of the new joint table. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictRightSeedAt_child_code
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) :
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictRightSeedAt A
      strategy hwin initial entry input member).child.1 =
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictRightLiteralChildAt
        A strategy initial entry input).code A := by
  let seed :=
    profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictRightSeedAt A
      strategy hwin initial entry input member
  calc
    seed.child.1 =
        let two :=
          profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryTwoInitial A
            strategy hwin initial entry member
        (profiledRawJointGuardedCommonRightLiteralCrossReceiverRecv A
          (two.2.2.candidate two.1) input.2 input.1).1.target .both :=
      seed.target_eq
    _ =
        (profiledRawJointHybridExactRightUniformActivation A strategy hwin
          (profiledRawJointGuardedCommonPointInstalled A strategy initial)
          ).target .both [(entry.2, entry.1)] (input.2, input.1) :=
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryInitial_strictRight_target
        A strategy hwin initial entry input member
    _ =
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictRightLiteralChildAt
          A strategy initial entry input).code A := by
      symm
      exact
        profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictRightLiteralChildAt_code
          A strategy hwin initial entry input

/-! ## Globally finite endpoint states installed by the receive -/

/-- Fixed process-one state alphabet during the following right block.  It
depends on the automaton and finite physical alphabets, but not on `initial`,
`entry`, `input`, a semantic child, or a policy. -/
noncomputable abbrev
    ProfiledRawJointStrictLeftPostResolveFiniteSenderState :=
  FiniteCrossAnchorDescriptorSenderState
    (profiledRawJointStrictLeftPostResolveFiniteMonitor A)

/-- Fixed informed-process-two state alphabet for that right block. -/
noncomputable abbrev
    ProfiledRawJointStrictLeftPostResolveFiniteReceiverState :=
  FiniteCrossAnchorDescriptorReceiverState
    (profiledRawJointStrictLeftPostResolveFiniteMonitor A)

noncomputable instance :
    Fintype (ProfiledRawJointStrictLeftPostResolveFiniteSenderState A) := by
  classical
  infer_instance

noncomputable instance :
    Fintype (ProfiledRawJointStrictLeftPostResolveFiniteReceiverState A) := by
  classical
  infer_instance

/-- Fixed process-two state alphabet during the mirrored left block. -/
noncomputable abbrev
    ProfiledRawJointStrictRightPostResolveFiniteSenderState :=
  FiniteCrossAnchorDescriptorSenderState
    (profiledRawJointStrictRightPostResolveFiniteMonitor A)

/-- Fixed informed-process-one state alphabet for the mirrored left block. -/
noncomputable abbrev
    ProfiledRawJointStrictRightPostResolveFiniteReceiverState :=
  FiniteCrossAnchorDescriptorReceiverState
    (profiledRawJointStrictRightPostResolveFiniteMonitor A)

noncomputable instance :
    Fintype (ProfiledRawJointStrictRightPostResolveFiniteSenderState A) := by
  classical
  infer_instance

noncomputable instance :
    Fintype (ProfiledRawJointStrictRightPostResolveFiniteReceiverState A) := by
  classical
  infer_instance

/-- The resolving receive installs one process-one joint move and its shared
blind-sender root.  The old bootstrap member is deliberately not an
argument: the preceding child-code lemma shows that either value reaches the
same semantic occurrence. -/
noncomputable def profiledRawJointStrictLeftPostResolveFiniteSenderInitial
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    ProfiledRawJointStrictLeftPostResolveFiniteSenderState A :=
  finiteCrossAnchorDescriptorSenderInitial
    (profiledRawJointStrictLeftPostResolveFiniteMonitor A)
    (profiledRawJointStrictLeftPostResolveFiniteMove A strategy hwin initial
      entry input)

/-- The informed endpoint installs the same move.  `false` selects the exact
strict-left literal child and `true` the simultaneous semantic child. -/
noncomputable def profiledRawJointStrictLeftPostResolveFiniteReceiverInitial
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (branch : Bool) :
    ProfiledRawJointStrictLeftPostResolveFiniteReceiverState A :=
  finiteCrossAnchorDescriptorReceiverInitial
    (profiledRawJointStrictLeftPostResolveFiniteMonitor A)
    (profiledRawJointStrictLeftPostResolveFiniteMove A strategy hwin initial
      entry input) branch

/-- Mirrored process-two installation. -/
noncomputable def profiledRawJointStrictRightPostResolveFiniteSenderInitial
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    ProfiledRawJointStrictRightPostResolveFiniteSenderState A :=
  finiteCrossAnchorDescriptorSenderInitial
    (profiledRawJointStrictRightPostResolveFiniteMonitor A)
    (profiledRawJointStrictRightPostResolveFiniteMove A strategy hwin initial
      entry input)

/-- Mirrored informed endpoint; again `false` is strict and `true` is
simultaneous. -/
noncomputable def profiledRawJointStrictRightPostResolveFiniteReceiverInitial
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (branch : Bool) :
    ProfiledRawJointStrictRightPostResolveFiniteReceiverState A :=
  finiteCrossAnchorDescriptorReceiverInitial
    (profiledRawJointStrictRightPostResolveFiniteMonitor A)
    (profiledRawJointStrictRightPostResolveFiniteMove A strategy hwin initial
      entry input) branch

@[simp] theorem profiledRawJointStrictLeftPostResolveFiniteSenderInitial_move
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    (profiledRawJointStrictLeftPostResolveFiniteSenderInitial A strategy hwin
      initial entry input).1 =
      profiledRawJointStrictLeftPostResolveFiniteMove A strategy hwin initial
        entry input :=
  rfl

@[simp] theorem profiledRawJointStrictLeftPostResolveFiniteReceiverInitial_move
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (branch : Bool) :
    (profiledRawJointStrictLeftPostResolveFiniteReceiverInitial A strategy hwin
      initial entry input branch).1 =
      profiledRawJointStrictLeftPostResolveFiniteMove A strategy hwin initial
        entry input :=
  rfl

@[simp] theorem
    profiledRawJointStrictLeftPostResolveFiniteReceiverInitial_branch
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (branch : Bool) :
    (profiledRawJointStrictLeftPostResolveFiniteReceiverInitial A strategy hwin
      initial entry input branch).2.1 = branch :=
  rfl

@[simp] theorem profiledRawJointStrictRightPostResolveFiniteSenderInitial_move
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    (profiledRawJointStrictRightPostResolveFiniteSenderInitial A strategy hwin
      initial entry input).1 =
      profiledRawJointStrictRightPostResolveFiniteMove A strategy hwin initial
        entry input :=
  rfl

@[simp] theorem
    profiledRawJointStrictRightPostResolveFiniteReceiverInitial_move
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (branch : Bool) :
    (profiledRawJointStrictRightPostResolveFiniteReceiverInitial A strategy hwin
      initial entry input branch).1 =
      profiledRawJointStrictRightPostResolveFiniteMove A strategy hwin initial
        entry input :=
  rfl

@[simp] theorem
    profiledRawJointStrictRightPostResolveFiniteReceiverInitial_branch
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (branch : Bool) :
    (profiledRawJointStrictRightPostResolveFiniteReceiverInitial A strategy hwin
      initial entry input branch).2.1 = branch :=
  rfl

/-! ## Shared-control invariant through every blind step -/

/-- Equality of installed moves and heterogeneous equality of their dependent
table controls. -/
def ProfiledRawJointStrictLeftPostResolveFiniteSynchronized
    (sender : ProfiledRawJointStrictLeftPostResolveFiniteSenderState A)
    (receiver : ProfiledRawJointStrictLeftPostResolveFiniteReceiverState A) :
    Prop :=
  sender.1 = receiver.1 ∧ HEq sender.2 receiver.2.2.1

/-- Mirrored synchronization predicate. -/
def ProfiledRawJointStrictRightPostResolveFiniteSynchronized
    (sender : ProfiledRawJointStrictRightPostResolveFiniteSenderState A)
    (receiver : ProfiledRawJointStrictRightPostResolveFiniteReceiverState A) :
    Prop :=
  sender.1 = receiver.1 ∧ HEq sender.2 receiver.2.2.1

/-- Both endpoints start with the same process-one move and control, for
either strict/common interpretation. -/
theorem profiledRawJointStrictLeftPostResolveFiniteInitial_synchronized
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (branch : Bool) :
    ProfiledRawJointStrictLeftPostResolveFiniteSynchronized A
      (profiledRawJointStrictLeftPostResolveFiniteSenderInitial A strategy hwin
        initial entry input)
      (profiledRawJointStrictLeftPostResolveFiniteReceiverInitial A strategy
        hwin initial entry input branch) := by
  constructor
  · rfl
  · exact heq_of_eq (finiteCrossAnchorDescriptor_initial_controls_eq
      (profiledRawJointStrictLeftPostResolveFiniteMonitor A)
      (profiledRawJointStrictLeftPostResolveFiniteMove A strategy hwin initial
        entry input) branch)

/-- Mirrored initial synchronization. -/
theorem profiledRawJointStrictRightPostResolveFiniteInitial_synchronized
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (branch : Bool) :
    ProfiledRawJointStrictRightPostResolveFiniteSynchronized A
      (profiledRawJointStrictRightPostResolveFiniteSenderInitial A strategy hwin
        initial entry input)
      (profiledRawJointStrictRightPostResolveFiniteReceiverInitial A strategy
        hwin initial entry input branch) := by
  constructor
  · rfl
  · exact heq_of_eq (finiteCrossAnchorDescriptor_initial_controls_eq
      (profiledRawJointStrictRightPostResolveFiniteMonitor A)
      (profiledRawJointStrictRightPostResolveFiniteMove A strategy hwin initial
        entry input) branch)

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- One right-block step preserves the shared move/control invariant.  The
blind sender sees only `delivered`; the informed receiver uses its own input,
the delivered sender input, and its stored branch. -/
theorem profiledRawJointStrictLeftPostResolveFiniteStep_synchronized
    (sender : ProfiledRawJointStrictLeftPostResolveFiniteSenderState A)
    (receiver : ProfiledRawJointStrictLeftPostResolveFiniteReceiverState A)
    (hsync : ProfiledRawJointStrictLeftPostResolveFiniteSynchronized A sender
      receiver)
    (own : In₂) (delivered : In₁) :
    ProfiledRawJointStrictLeftPostResolveFiniteSynchronized A
      (finiteCrossAnchorDescriptorSenderStep
        (profiledRawJointStrictLeftPostResolveFiniteMonitor A) sender
        delivered).2
      (finiteCrossAnchorDescriptorReceiverRecv
        (profiledRawJointStrictLeftPostResolveFiniteMonitor A) receiver own
        delivered).2 := by
  constructor
  · simpa using hsync.1
  · exact finiteCrossAnchorDescriptor_step_controls_eq
      (profiledRawJointStrictLeftPostResolveFiniteMonitor A) sender receiver
      hsync.1 hsync.2 own delivered

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Mirrored left-block step closure. -/
theorem profiledRawJointStrictRightPostResolveFiniteStep_synchronized
    (sender : ProfiledRawJointStrictRightPostResolveFiniteSenderState A)
    (receiver : ProfiledRawJointStrictRightPostResolveFiniteReceiverState A)
    (hsync : ProfiledRawJointStrictRightPostResolveFiniteSynchronized A sender
      receiver)
    (own : In₁) (delivered : In₂) :
    ProfiledRawJointStrictRightPostResolveFiniteSynchronized A
      (finiteCrossAnchorDescriptorSenderStep
        (profiledRawJointStrictRightPostResolveFiniteMonitor A) sender
        delivered).2
      (finiteCrossAnchorDescriptorReceiverRecv
        (profiledRawJointStrictRightPostResolveFiniteMonitor A) receiver own
        delivered).2 := by
  constructor
  · simpa using hsync.1
  · exact finiteCrossAnchorDescriptor_step_controls_eq
      (profiledRawJointStrictRightPostResolveFiniteMonitor A) sender receiver
      hsync.1 hsync.2 own delivered

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- At every reachable control, the process-one blind output is the sender
coordinate of both the strict and simultaneous member tables. -/
theorem profiledRawJointStrictLeftPostResolveFiniteSender_output_eq_member
    (sender : ProfiledRawJointStrictLeftPostResolveFiniteSenderState A)
    (input : In₁) (branch : Bool) :
    (finiteCrossAnchorDescriptorSenderStep
      (profiledRawJointStrictLeftPostResolveFiniteMonitor A) sender input).1 =
      ((sender.1.memberController
        (profiledRawJointStrictLeftPostResolveFiniteMonitor A) branch).labelOf
          sender.2).1 input :=
  finiteCrossAnchorDescriptorSenderStep_output_eq_member
    (profiledRawJointStrictLeftPostResolveFiniteMonitor A) sender input branch

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Mirrored blind-output coherence. -/
theorem profiledRawJointStrictRightPostResolveFiniteSender_output_eq_member
    (sender : ProfiledRawJointStrictRightPostResolveFiniteSenderState A)
    (input : In₂) (branch : Bool) :
    (finiteCrossAnchorDescriptorSenderStep
      (profiledRawJointStrictRightPostResolveFiniteMonitor A) sender input).1 =
      ((sender.1.memberController
        (profiledRawJointStrictRightPostResolveFiniteMonitor A) branch).labelOf
          sender.2).1 input :=
  finiteCrossAnchorDescriptorSenderStep_output_eq_member
    (profiledRawJointStrictRightPostResolveFiniteMonitor A) sender input branch

/-! ## Receive-created forks and arbitrary blind prefixes -/

/-- Replacement for the old process-one strict/common postcontrol fork.  The
blind endpoint's two components are definitionally the same globally finite
state.  The obsolete bootstrap member is accepted only to make the intended
replacement point explicit; it is not stored. -/
noncomputable def profiledRawJointStrictLeftPostResolveFiniteSenderFork
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (_member : Bool) :
    FiniteDelayedFork
      (ProfiledRawJointStrictLeftPostResolveFiniteSenderState A) :=
  let state := profiledRawJointStrictLeftPostResolveFiniteSenderInitial A
    strategy hwin initial entry input
  ⟨state, state⟩

/-- Replacement fork for the mirrored process-two case. -/
noncomputable def profiledRawJointStrictRightPostResolveFiniteSenderFork
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (_member : Bool) :
    FiniteDelayedFork
      (ProfiledRawJointStrictRightPostResolveFiniteSenderState A) :=
  let state := profiledRawJointStrictRightPostResolveFiniteSenderInitial A
    strategy hwin initial entry input
  ⟨state, state⟩

/-- Open and simultaneous interpretations install literally the same blind
process-one control at the resolving receive. -/
@[simp] theorem profiledRawJointStrictLeftPostResolveFiniteSenderFork_eq
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) :
    (profiledRawJointStrictLeftPostResolveFiniteSenderFork A strategy hwin
      initial entry input member).openControl =
      (profiledRawJointStrictLeftPostResolveFiniteSenderFork A strategy hwin
        initial entry input member).closedControl :=
  rfl

/-- Mirrored literal equality of the two blind postcontrols. -/
@[simp] theorem profiledRawJointStrictRightPostResolveFiniteSenderFork_eq
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) :
    (profiledRawJointStrictRightPostResolveFiniteSenderFork A strategy hwin
      initial entry input member).openControl =
      (profiledRawJointStrictRightPostResolveFiniteSenderFork A strategy hwin
        initial entry input member).closedControl :=
  rfl

/-- The replacement postcontrol is also independent of the old bootstrap
member. -/
theorem profiledRawJointStrictLeftPostResolveFiniteSenderFork_member_independent
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (left right : Bool) :
    profiledRawJointStrictLeftPostResolveFiniteSenderFork A strategy hwin
      initial entry input left =
      profiledRawJointStrictLeftPostResolveFiniteSenderFork A strategy hwin
        initial entry input right :=
  rfl

/-- Mirrored member independence. -/
theorem
    profiledRawJointStrictRightPostResolveFiniteSenderFork_member_independent
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (left right : Bool) :
    profiledRawJointStrictRightPostResolveFiniteSenderFork A strategy hwin
      initial entry input left =
      profiledRawJointStrictRightPostResolveFiniteSenderFork A strategy hwin
        initial entry input right :=
  rfl

/-- The open component synchronizes with the informed endpoint's strict
member at the concrete process-one resolving receive. -/
theorem profiledRawJointStrictLeftPostResolveFiniteSenderFork_open_synchronized
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) :
    ProfiledRawJointStrictLeftPostResolveFiniteSynchronized A
      (profiledRawJointStrictLeftPostResolveFiniteSenderFork A strategy hwin
        initial entry input member).openControl
      (profiledRawJointStrictLeftPostResolveFiniteReceiverInitial A strategy
        hwin initial entry input false) :=
  profiledRawJointStrictLeftPostResolveFiniteInitial_synchronized A strategy
    hwin initial entry input false

/-- The closed component synchronizes with the simultaneous member of the
same installed move. -/
theorem
    profiledRawJointStrictLeftPostResolveFiniteSenderFork_closed_synchronized
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) :
    ProfiledRawJointStrictLeftPostResolveFiniteSynchronized A
      (profiledRawJointStrictLeftPostResolveFiniteSenderFork A strategy hwin
        initial entry input member).closedControl
      (profiledRawJointStrictLeftPostResolveFiniteReceiverInitial A strategy
        hwin initial entry input true) :=
  profiledRawJointStrictLeftPostResolveFiniteInitial_synchronized A strategy
    hwin initial entry input true

/-- Strict member synchronization for the mirrored receive. -/
theorem
    profiledRawJointStrictRightPostResolveFiniteSenderFork_open_synchronized
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) :
    ProfiledRawJointStrictRightPostResolveFiniteSynchronized A
      (profiledRawJointStrictRightPostResolveFiniteSenderFork A strategy hwin
        initial entry input member).openControl
      (profiledRawJointStrictRightPostResolveFiniteReceiverInitial A strategy
        hwin initial entry input false) :=
  profiledRawJointStrictRightPostResolveFiniteInitial_synchronized A strategy
    hwin initial entry input false

/-- Simultaneous member synchronization for the mirrored receive. -/
theorem
    profiledRawJointStrictRightPostResolveFiniteSenderFork_closed_synchronized
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) :
    ProfiledRawJointStrictRightPostResolveFiniteSynchronized A
      (profiledRawJointStrictRightPostResolveFiniteSenderFork A strategy hwin
        initial entry input member).closedControl
      (profiledRawJointStrictRightPostResolveFiniteReceiverInitial A strategy
        hwin initial entry input true) :=
  profiledRawJointStrictRightPostResolveFiniteInitial_synchronized A strategy
    hwin initial entry input true

/-- Execute a finite right block, retaining just the two endpoint states.
Each list element is the informed endpoint's own input followed by the
delivered blind-sender input. -/
noncomputable def profiledRawJointStrictLeftPostResolveFiniteRun :
    (ProfiledRawJointStrictLeftPostResolveFiniteSenderState A ×
      ProfiledRawJointStrictLeftPostResolveFiniteReceiverState A) →
      List (In₂ × In₁) →
      (ProfiledRawJointStrictLeftPostResolveFiniteSenderState A ×
        ProfiledRawJointStrictLeftPostResolveFiniteReceiverState A)
  | state, [] => state
  | state, round :: rest =>
      profiledRawJointStrictLeftPostResolveFiniteRun
        ((finiteCrossAnchorDescriptorSenderStep
            (profiledRawJointStrictLeftPostResolveFiniteMonitor A) state.1
            round.2).2,
          (finiteCrossAnchorDescriptorReceiverRecv
            (profiledRawJointStrictLeftPostResolveFiniteMonitor A) state.2
            round.1 round.2).2) rest

/-- Execute a finite mirrored left block. -/
noncomputable def profiledRawJointStrictRightPostResolveFiniteRun :
    (ProfiledRawJointStrictRightPostResolveFiniteSenderState A ×
      ProfiledRawJointStrictRightPostResolveFiniteReceiverState A) →
      List (In₁ × In₂) →
      (ProfiledRawJointStrictRightPostResolveFiniteSenderState A ×
        ProfiledRawJointStrictRightPostResolveFiniteReceiverState A)
  | state, [] => state
  | state, round :: rest =>
      profiledRawJointStrictRightPostResolveFiniteRun
        ((finiteCrossAnchorDescriptorSenderStep
            (profiledRawJointStrictRightPostResolveFiniteMonitor A) state.1
            round.2).2,
          (finiteCrossAnchorDescriptorReceiverRecv
            (profiledRawJointStrictRightPostResolveFiniteMonitor A) state.2
            round.1 round.2).2) rest

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Synchronization is preserved through an arbitrary finite right block. -/
theorem profiledRawJointStrictLeftPostResolveFiniteRun_synchronized
    (state : ProfiledRawJointStrictLeftPostResolveFiniteSenderState A ×
      ProfiledRawJointStrictLeftPostResolveFiniteReceiverState A)
    (hsync : ProfiledRawJointStrictLeftPostResolveFiniteSynchronized A state.1
      state.2) (past : List (In₂ × In₁)) :
    ProfiledRawJointStrictLeftPostResolveFiniteSynchronized A
      (profiledRawJointStrictLeftPostResolveFiniteRun A state past).1
      (profiledRawJointStrictLeftPostResolveFiniteRun A state past).2 := by
  induction past generalizing state with
  | nil => exact hsync
  | cons round rest ih =>
      apply ih
      exact profiledRawJointStrictLeftPostResolveFiniteStep_synchronized A
        state.1 state.2 hsync round.1 round.2

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Mirrored arbitrary-prefix synchronization. -/
theorem profiledRawJointStrictRightPostResolveFiniteRun_synchronized
    (state : ProfiledRawJointStrictRightPostResolveFiniteSenderState A ×
      ProfiledRawJointStrictRightPostResolveFiniteReceiverState A)
    (hsync : ProfiledRawJointStrictRightPostResolveFiniteSynchronized A state.1
      state.2) (past : List (In₁ × In₂)) :
    ProfiledRawJointStrictRightPostResolveFiniteSynchronized A
      (profiledRawJointStrictRightPostResolveFiniteRun A state past).1
      (profiledRawJointStrictRightPostResolveFiniteRun A state past).2 := by
  induction past generalizing state with
  | nil => exact hsync
  | cons round rest ih =>
      apply ih
      exact profiledRawJointStrictRightPostResolveFiniteStep_synchronized A
        state.1 state.2 hsync round.1 round.2

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

/-- The informed endpoint's strict/common member is never restarted or
changed during the right block. -/
theorem profiledRawJointStrictLeftPostResolveFiniteRun_branch
    (state : ProfiledRawJointStrictLeftPostResolveFiniteSenderState A ×
      ProfiledRawJointStrictLeftPostResolveFiniteReceiverState A)
    (past : List (In₂ × In₁)) :
    (profiledRawJointStrictLeftPostResolveFiniteRun A state past).2.2.1 =
      state.2.2.1 := by
  induction past generalizing state with
  | nil => rfl
  | cons round rest ih =>
      rw [profiledRawJointStrictLeftPostResolveFiniteRun]
      exact ih _

/-- Mirrored persistence of the stored member. -/
theorem profiledRawJointStrictRightPostResolveFiniteRun_branch
    (state : ProfiledRawJointStrictRightPostResolveFiniteSenderState A ×
      ProfiledRawJointStrictRightPostResolveFiniteReceiverState A)
    (past : List (In₁ × In₂)) :
    (profiledRawJointStrictRightPostResolveFiniteRun A state past).2.2.1 =
      state.2.2.1 := by
  induction past generalizing state with
  | nil => rfl
  | cons round rest ih =>
      rw [profiledRawJointStrictRightPostResolveFiniteRun]
      exact ih _

/-- The installed move itself is unchanged throughout a process-one right
block. -/
theorem profiledRawJointStrictLeftPostResolveFiniteRun_move
    (state : ProfiledRawJointStrictLeftPostResolveFiniteSenderState A ×
      ProfiledRawJointStrictLeftPostResolveFiniteReceiverState A)
    (past : List (In₂ × In₁)) :
    (profiledRawJointStrictLeftPostResolveFiniteRun A state past).2.1 =
      state.2.1 := by
  induction past generalizing state with
  | nil => rfl
  | cons round rest ih =>
      rw [profiledRawJointStrictLeftPostResolveFiniteRun]
      exact ih _

/-- Mirrored persistence of the installed move. -/
theorem profiledRawJointStrictRightPostResolveFiniteRun_move
    (state : ProfiledRawJointStrictRightPostResolveFiniteSenderState A ×
      ProfiledRawJointStrictRightPostResolveFiniteReceiverState A)
    (past : List (In₁ × In₂)) :
    (profiledRawJointStrictRightPostResolveFiniteRun A state past).2.1 =
      state.2.1 := by
  induction past generalizing state with
  | nil => rfl
  | cons round rest ih =>
      rw [profiledRawJointStrictRightPostResolveFiniteRun]
      exact ih _

end

/-! ## The stored Boolean has the intended semantic readback -/

/-- Reading member `false` of the process-one installation gives the exact
strict-left literal-child invariant after every finite prefix. -/
noncomputable abbrev profiledRawJointStrictLeftPostResolveFinite_false_readback
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (env : Nat → In₂ × In₁) (n : Nat) (row : PairedEntryRow) :=
  profiledRawJointStrictLeftPostResolveFiniteMove_strictTarget A strategy hwin
    initial entry input env n row

/-- Reading member `true` gives the simultaneous-successor invariant after
every finite prefix. -/
noncomputable abbrev profiledRawJointStrictLeftPostResolveFinite_true_readback
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (env : Nat → In₂ × In₁) (n : Nat) (row : PairedEntryRow) :=
  profiledRawJointStrictLeftPostResolveFiniteMove_commonTarget A strategy hwin
    initial entry input env n row

/-- Strict-right mirror of the `false` readback. -/
noncomputable abbrev profiledRawJointStrictRightPostResolveFinite_false_readback
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (env : Nat → In₁ × In₂) (n : Nat) (row : PairedEntryRow) :=
  profiledRawJointStrictRightPostResolveFiniteMove_strictTarget A strategy hwin
    initial entry input env n row

/-- Simultaneous mirror of the `true` readback. -/
noncomputable abbrev profiledRawJointStrictRightPostResolveFinite_true_readback
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (env : Nat → In₁ × In₂) (n : Nat) (row : PairedEntryRow) :=
  profiledRawJointStrictRightPostResolveFiniteMove_commonTarget A strategy hwin
    initial entry input env n row

end

end DetParityAutomaton

end DistributedSynthesis
