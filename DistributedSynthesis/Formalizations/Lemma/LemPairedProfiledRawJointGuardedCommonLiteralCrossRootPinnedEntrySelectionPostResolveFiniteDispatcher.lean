/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteCrossAnchorLocalCarrierReachability
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionPostResolveFiniteInstallation

/-!
# Receive dispatch from the finite post-resolve carrier

This file executes a concrete round from an arbitrarily advanced post-resolve
endpoint pair.  The blind endpoint advances its one shared sender control;
the informed endpoint reads the strict/common member stored at the resolving
receive, advances that member's current monitor state, and returns both its
physical output and its finite target table.  No transition restarts a
monitor, and no current graph or semantic history is an executable argument.

The proof-side reachability relation identifies every dispatcher call reached
from an installed root with one exact node of the selected member's narrowed
tree.  Consequently every returned closing target has the semantic meaning
selected by the stored member.
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

private abbrev LeftSenderState :=
  ProfiledRawJointStrictLeftPostResolveFiniteSenderState A

private abbrev LeftReceiverState :=
  ProfiledRawJointStrictLeftPostResolveFiniteReceiverState A

private abbrev RightSenderState :=
  ProfiledRawJointStrictRightPostResolveFiniteSenderState A

private abbrev RightReceiverState :=
  ProfiledRawJointStrictRightPostResolveFiniteReceiverState A

/-! ## Total finite dispatchers -/

/-- Result of one process-one-blind right-block round.  The full certified
receiver output is retained so a later row selection can consume its target. -/
structure ProfiledRawJointStrictLeftPostResolveFiniteDispatchResult where
  senderOutput : Out₁
  receiverOutput : ProfiledRawJointTargetRightReceiverOutput
    (Out₁ := Out₁) (Out₂ := Out₂) (ProfiledRawJointUnitTarget A)
  nextSender : LeftSenderState A
  nextReceiver : LeftReceiverState A

/-- Mirrored process-two-blind result. -/
structure ProfiledRawJointStrictRightPostResolveFiniteDispatchResult where
  senderOutput : Out₂
  receiverOutput : ProfiledRawJointTargetLeftReceiverOutput
    (Out₁ := Out₁) (Out₂ := Out₂) (ProfiledRawJointUnitTarget A)
  nextSender : RightSenderState A
  nextReceiver : RightReceiverState A

/-- Execute the current right-block member stored by process two. -/
noncomputable def profiledRawJointStrictLeftPostResolveFiniteDispatch
    (state : LeftSenderState A × LeftReceiverState A)
    (own : In₂) (delivered : In₁) :
    ProfiledRawJointStrictLeftPostResolveFiniteDispatchResult A :=
  let senderStep := finiteCrossAnchorDescriptorSenderStep
    (profiledRawJointStrictLeftPostResolveFiniteMonitor A) state.1 delivered
  let receiverStep := finiteCrossAnchorDescriptorReceiverRecv
    (profiledRawJointStrictLeftPostResolveFiniteMonitor A) state.2 own delivered
  ⟨senderStep.1, receiverStep.1, senderStep.2, receiverStep.2⟩

/-- Execute the mirrored left-block member stored by process one. -/
noncomputable def profiledRawJointStrictRightPostResolveFiniteDispatch
    (state : RightSenderState A × RightReceiverState A)
    (own : In₁) (delivered : In₂) :
    ProfiledRawJointStrictRightPostResolveFiniteDispatchResult A :=
  let senderStep := finiteCrossAnchorDescriptorSenderStep
    (profiledRawJointStrictRightPostResolveFiniteMonitor A) state.1 delivered
  let receiverStep := finiteCrossAnchorDescriptorReceiverRecv
    (profiledRawJointStrictRightPostResolveFiniteMonitor A) state.2 own delivered
  ⟨senderStep.1, receiverStep.1, senderStep.2, receiverStep.2⟩

/-- Physical output pair of a right-block dispatch. -/
def ProfiledRawJointStrictLeftPostResolveFiniteDispatchResult.physical
    (result : ProfiledRawJointStrictLeftPostResolveFiniteDispatchResult A) :
    Out₁ × Out₂ :=
  (result.senderOutput,
    profiledRawJointTargetRightReceiverBothPhysicalOutput result.receiverOutput)

/-- Physical output pair of a mirrored left-block dispatch. -/
def ProfiledRawJointStrictRightPostResolveFiniteDispatchResult.physical
    (result : ProfiledRawJointStrictRightPostResolveFiniteDispatchResult A) :
    Out₁ × Out₂ :=
  (profiledRawJointTargetLeftReceiverBothPhysicalOutput result.receiverOutput,
    result.senderOutput)

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- The returned target is evaluated by the member and monitor state stored
in the informed endpoint before the step. -/
theorem profiledRawJointStrictLeftPostResolveFiniteDispatch_target_eq_label
    (state : LeftSenderState A × LeftReceiverState A)
    (own : In₂) (delivered : In₁) (row : PairedEntryRow) :
    (profiledRawJointStrictLeftPostResolveFiniteDispatch A state own delivered
      ).receiverOutput.target row =
      (((state.2.1.memberController
        (profiledRawJointStrictLeftPostResolveFiniteMonitor A)
        state.2.2.1).labelOf state.2.2.2.1).2 state.2.2.2.2
          (own, delivered)).target row :=
  rfl

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Mirrored selected-label equation. -/
theorem profiledRawJointStrictRightPostResolveFiniteDispatch_target_eq_label
    (state : RightSenderState A × RightReceiverState A)
    (own : In₁) (delivered : In₂) (row : PairedEntryRow) :
    (profiledRawJointStrictRightPostResolveFiniteDispatch A state own delivered
      ).receiverOutput.target row =
      (((state.2.1.memberController
        (profiledRawJointStrictRightPostResolveFiniteMonitor A)
        state.2.2.1).labelOf state.2.2.2.1).2 state.2.2.2.2
          (own, delivered)).target row :=
  rfl

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- A dispatcher call preserves the synchronized move/control invariant. -/
theorem profiledRawJointStrictLeftPostResolveFiniteDispatch_synchronized
    (state : LeftSenderState A × LeftReceiverState A)
    (hsync : ProfiledRawJointStrictLeftPostResolveFiniteSynchronized A state.1
      state.2) (own : In₂) (delivered : In₁) :
    let result :=
      profiledRawJointStrictLeftPostResolveFiniteDispatch A state own delivered
    ProfiledRawJointStrictLeftPostResolveFiniteSynchronized A
      result.nextSender result.nextReceiver := by
  dsimp only [profiledRawJointStrictLeftPostResolveFiniteDispatch]
  exact profiledRawJointStrictLeftPostResolveFiniteStep_synchronized A state.1
    state.2 hsync own delivered

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Mirrored synchronization preservation. -/
theorem profiledRawJointStrictRightPostResolveFiniteDispatch_synchronized
    (state : RightSenderState A × RightReceiverState A)
    (hsync : ProfiledRawJointStrictRightPostResolveFiniteSynchronized A state.1
      state.2) (own : In₁) (delivered : In₂) :
    let result :=
      profiledRawJointStrictRightPostResolveFiniteDispatch A state own delivered
    ProfiledRawJointStrictRightPostResolveFiniteSynchronized A
      result.nextSender result.nextReceiver := by
  dsimp only [profiledRawJointStrictRightPostResolveFiniteDispatch]
  exact profiledRawJointStrictRightPostResolveFiniteStep_synchronized A state.1
    state.2 hsync own delivered

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem profiledRawJointStrictLeftPostResolveFiniteDispatch_branch
    (state : LeftSenderState A × LeftReceiverState A)
    (own : In₂) (delivered : In₁) :
    (profiledRawJointStrictLeftPostResolveFiniteDispatch A state own delivered
      ).nextReceiver.2.1 = state.2.2.1 :=
  rfl

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem profiledRawJointStrictRightPostResolveFiniteDispatch_branch
    (state : RightSenderState A × RightReceiverState A)
    (own : In₁) (delivered : In₂) :
    (profiledRawJointStrictRightPostResolveFiniteDispatch A state own delivered
      ).nextReceiver.2.1 = state.2.2.1 :=
  rfl

/-! ## Reachability from the concrete installation -/

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- The finite right-block runner preserves exact local tree reachability. -/
theorem profiledRawJointStrictLeftPostResolveFiniteRun_preserves_reachable
    (state : LeftSenderState A × LeftReceiverState A)
    (hreach : FiniteCrossAnchorDescriptorLocallyReachable
      (profiledRawJointStrictLeftPostResolveFiniteMonitor A) state.1 state.2)
    (past : List (In₂ × In₁)) :
    FiniteCrossAnchorDescriptorLocallyReachable
      (profiledRawJointStrictLeftPostResolveFiniteMonitor A)
      (profiledRawJointStrictLeftPostResolveFiniteRun A state past).1
      (profiledRawJointStrictLeftPostResolveFiniteRun A state past).2 := by
  induction past generalizing state with
  | nil => exact hreach
  | cons round rest ih =>
      apply ih
      exact hreach.step
        (profiledRawJointStrictLeftPostResolveFiniteMonitor A) round

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Mirrored reachability preservation. -/
theorem profiledRawJointStrictRightPostResolveFiniteRun_preserves_reachable
    (state : RightSenderState A × RightReceiverState A)
    (hreach : FiniteCrossAnchorDescriptorLocallyReachable
      (profiledRawJointStrictRightPostResolveFiniteMonitor A) state.1 state.2)
    (past : List (In₁ × In₂)) :
    FiniteCrossAnchorDescriptorLocallyReachable
      (profiledRawJointStrictRightPostResolveFiniteMonitor A)
      (profiledRawJointStrictRightPostResolveFiniteRun A state past).1
      (profiledRawJointStrictRightPostResolveFiniteRun A state past).2 := by
  induction past generalizing state with
  | nil => exact hreach
  | cons round rest ih =>
      apply ih
      exact hreach.step
        (profiledRawJointStrictRightPostResolveFiniteMonitor A) round

/-- Every process-one state reached from the resolving receive has a common
full-input prefix witness in the installed member tree. -/
theorem profiledRawJointStrictLeftPostResolveFiniteRun_reachable
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (branch : Bool) (past : List (In₂ × In₁)) :
    let start : LeftSenderState A × LeftReceiverState A :=
      (profiledRawJointStrictLeftPostResolveFiniteSenderInitial A strategy hwin
          initial entry input,
        profiledRawJointStrictLeftPostResolveFiniteReceiverInitial A strategy
          hwin initial entry input branch)
    FiniteCrossAnchorDescriptorLocallyReachable
      (profiledRawJointStrictLeftPostResolveFiniteMonitor A)
      (profiledRawJointStrictLeftPostResolveFiniteRun A start past).1
      (profiledRawJointStrictLeftPostResolveFiniteRun A start past).2 := by
  dsimp only
  apply profiledRawJointStrictLeftPostResolveFiniteRun_preserves_reachable A
  exact finiteCrossAnchorDescriptorLocallyReachable_initial
    (profiledRawJointStrictLeftPostResolveFiniteMonitor A)
    (profiledRawJointStrictLeftPostResolveFiniteMove A strategy hwin initial
      entry input) branch

/-- Mirrored reachability from the concrete resolving receive. -/
theorem profiledRawJointStrictRightPostResolveFiniteRun_reachable
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (branch : Bool) (past : List (In₁ × In₂)) :
    let start : RightSenderState A × RightReceiverState A :=
      (profiledRawJointStrictRightPostResolveFiniteSenderInitial A strategy hwin
          initial entry input,
        profiledRawJointStrictRightPostResolveFiniteReceiverInitial A strategy
          hwin initial entry input branch)
    FiniteCrossAnchorDescriptorLocallyReachable
      (profiledRawJointStrictRightPostResolveFiniteMonitor A)
      (profiledRawJointStrictRightPostResolveFiniteRun A start past).1
      (profiledRawJointStrictRightPostResolveFiniteRun A start past).2 := by
  dsimp only
  apply profiledRawJointStrictRightPostResolveFiniteRun_preserves_reachable A
  exact finiteCrossAnchorDescriptorLocallyReachable_initial
    (profiledRawJointStrictRightPostResolveFiniteMonitor A)
    (profiledRawJointStrictRightPostResolveFiniteMove A strategy hwin initial
      entry input) branch

/-! ## Exact selected-member round -/

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- At every reachable process-one state, the entire dispatcher letter—not
only its finite target—is the next letter of the stored member controller. -/
theorem profiledRawJointStrictLeftPostResolveFiniteDispatch_eq_treePlay_of_reachable
    (state : LeftSenderState A × LeftReceiverState A)
    (hreach : FiniteCrossAnchorDescriptorLocallyReachable
      (profiledRawJointStrictLeftPostResolveFiniteMonitor A) state.1 state.2)
    (current : In₂ × In₁) :
    ∃ past : List (In₂ × In₁),
      let move := state.2.1
      let branch := state.2.2.1
      let restarted :=
        (profiledRawJointStrictLeftPostResolveFiniteMonitor A
          (move.1.descriptor branch)).restartAt (move.1.start branch)
      let controller := move.memberController
        (profiledRawJointStrictLeftPostResolveFiniteMonitor A) branch
      let env : Nat → In₂ × In₁ :=
        DetParityAutomaton.omegaOfList (past ++ [current])
      (current,
        (profiledRawJointStrictLeftPostResolveFiniteDispatch A state current.1
          current.2).receiverOutput,
        (profiledRawJointStrictLeftPostResolveFiniteDispatch A state current.1
          current.2).senderOutput) =
        treePlay (narrowedInducedTree restarted controller.labeledTree) env
          past.length := by
  rcases hreach.exists_localRound_eq_treePlay
      (profiledRawJointStrictLeftPostResolveFiniteMonitor A) current with
    ⟨past, hsender, hreceiver, hround⟩
  refine ⟨past, ?_⟩
  simpa only [profiledRawJointStrictLeftPostResolveFiniteDispatch] using hround

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Mirrored exact selected-member dispatcher letter. -/
theorem profiledRawJointStrictRightPostResolveFiniteDispatch_eq_treePlay_of_reachable
    (state : RightSenderState A × RightReceiverState A)
    (hreach : FiniteCrossAnchorDescriptorLocallyReachable
      (profiledRawJointStrictRightPostResolveFiniteMonitor A) state.1 state.2)
    (current : In₁ × In₂) :
    ∃ past : List (In₁ × In₂),
      let move := state.2.1
      let branch := state.2.2.1
      let restarted :=
        (profiledRawJointStrictRightPostResolveFiniteMonitor A
          (move.1.descriptor branch)).restartAt (move.1.start branch)
      let controller := move.memberController
        (profiledRawJointStrictRightPostResolveFiniteMonitor A) branch
      let env : Nat → In₁ × In₂ :=
        DetParityAutomaton.omegaOfList (past ++ [current])
      (current,
        (profiledRawJointStrictRightPostResolveFiniteDispatch A state current.1
          current.2).receiverOutput,
        (profiledRawJointStrictRightPostResolveFiniteDispatch A state current.1
          current.2).senderOutput) =
        treePlay (narrowedInducedTree restarted controller.labeledTree) env
          past.length := by
  rcases hreach.exists_localRound_eq_treePlay
      (profiledRawJointStrictRightPostResolveFiniteMonitor A) current with
    ⟨past, hsender, hreceiver, hround⟩
  refine ⟨past, ?_⟩
  simpa only [profiledRawJointStrictRightPostResolveFiniteDispatch] using hround

/-! ## Semantic target selected at a reached dispatcher call -/

/-- Proof-side target obligation for one process-one dispatcher call.  The
wrapper keeps downstream theorem types independent of the internal dependent
carrier projections. -/
structure ProfiledRawJointStrictLeftPostResolveFiniteDispatchTargetMeaning
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (branch : Bool) (state : LeftSenderState A × LeftReceiverState A)
    (current : In₂ × In₁) (row : PairedEntryRow) : Prop where
  close : erasePairedProfiledState A
      (profiledRawJointUnitRightTargetProjection A
        ((profiledRawJointStrictLeftPostResolveFiniteDispatch A state current.1
          current.2).receiverOutput.target row)) =
    pairedRightCloseTarget A state.2.2.2.2.2.1 row
      (profiledRawJointTargetRightPhysicalLetter A
        (current,
          (profiledRawJointStrictLeftPostResolveFiniteDispatch A state
            current.1 current.2).receiverOutput,
          (profiledRawJointStrictLeftPostResolveFiniteDispatch A state
            current.1 current.2).senderOutput))
  meaning : ProfiledRawJointStrictLeftPostResolveFiniteTargetMeaning A strategy
    hwin initial entry input branch
      ((profiledRawJointStrictLeftPostResolveFiniteDispatch A state current.1
        current.2).receiverOutput.target row)

/-- Proof-side occurrence invariant needed to interpret a reached finite
state.  It is not part of either executable endpoint state. -/
structure ProfiledRawJointStrictLeftPostResolveFiniteInstalledReachable
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (branch : Bool) (state : LeftSenderState A × LeftReceiverState A) : Prop where
  reachable : FiniteCrossAnchorDescriptorLocallyReachable
    (profiledRawJointStrictLeftPostResolveFiniteMonitor A) state.1 state.2
  move_eq : state.2.1 =
    profiledRawJointStrictLeftPostResolveFiniteMove A strategy hwin initial
      entry input
  branch_eq : state.2.2.1 = branch

/- A locally reachable dispatcher state whose move and member come from the
concrete process-one installation returns a target with exactly the stored
member's meaning.  The preceding run lemmas provide these three hypotheses at
every finite depth. -/
theorem profiledRawJointStrictLeftPostResolveFiniteDispatch_targetMeaning_of_reachable
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (branch : Bool) (state : LeftSenderState A × LeftReceiverState A)
    (hstate : ProfiledRawJointStrictLeftPostResolveFiniteInstalledReachable A
      strategy hwin initial entry input branch state)
    (current : In₂ × In₁) (row : PairedEntryRow) :
    ProfiledRawJointStrictLeftPostResolveFiniteDispatchTargetMeaning A strategy
      hwin initial entry input branch state current row := by
  rcases state with ⟨sender, receiver⟩
  rcases receiver with ⟨move, anchor, control, monitorState⟩
  have hmove := hstate.move_eq
  have hbranch := hstate.branch_eq
  dsimp only at hmove hbranch
  subst move
  subst anchor
  rcases hstate.reachable.exists_localRound_and_monitorRun
      (profiledRawJointStrictLeftPostResolveFiniteMonitor A) current with
    ⟨witness, hround, hmonitor⟩
  let env : Nat → In₂ × In₁ :=
    DetParityAutomaton.omegaOfList (witness ++ [current])
  have hsafe :=
    profiledRawJointStrictLeftPostResolveFiniteMove_targetMeaning A strategy
      hwin initial entry input branch env witness.length row
  have hclose := hsafe.1
  have hmeaning := hsafe.2
  dsimp only at hround hmonitor
  rw [hmonitor] at hclose
  rw [← hround] at hclose hmeaning
  constructor
  · simpa only [profiledRawJointStrictLeftPostResolveFiniteDispatch] using
      hclose
  · simpa only [profiledRawJointStrictLeftPostResolveFiniteDispatch] using
      hmeaning

/-- Mirrored proof-side target obligation. -/
structure ProfiledRawJointStrictRightPostResolveFiniteDispatchTargetMeaning
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (branch : Bool) (state : RightSenderState A × RightReceiverState A)
    (current : In₁ × In₂) (row : PairedEntryRow) : Prop where
  close : erasePairedProfiledState A
      (profiledRawJointUnitLeftTargetProjection A
        ((profiledRawJointStrictRightPostResolveFiniteDispatch A state current.1
          current.2).receiverOutput.target row)) =
    pairedLeftCloseTarget A state.2.2.2.2.2.1 row
      (profiledRawJointTargetLeftPhysicalLetter A
        (current,
          (profiledRawJointStrictRightPostResolveFiniteDispatch A state
            current.1 current.2).receiverOutput,
          (profiledRawJointStrictRightPostResolveFiniteDispatch A state
            current.1 current.2).senderOutput))
  meaning : ProfiledRawJointStrictRightPostResolveFiniteTargetMeaning A strategy
    hwin initial entry input branch
      ((profiledRawJointStrictRightPostResolveFiniteDispatch A state current.1
        current.2).receiverOutput.target row)

/-- Mirrored occurrence invariant. -/
structure ProfiledRawJointStrictRightPostResolveFiniteInstalledReachable
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (branch : Bool)
    (state : RightSenderState A × RightReceiverState A) : Prop where
  reachable : FiniteCrossAnchorDescriptorLocallyReachable
    (profiledRawJointStrictRightPostResolveFiniteMonitor A) state.1 state.2
  move_eq : state.2.1 =
    profiledRawJointStrictRightPostResolveFiniteMove A strategy hwin initial
      entry input
  branch_eq : state.2.2.1 = branch

/-- The mirrored dispatcher also returns the meaning of its stored member. -/
theorem profiledRawJointStrictRightPostResolveFiniteDispatch_targetMeaning_of_reachable
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (branch : Bool) (state : RightSenderState A × RightReceiverState A)
    (hstate : ProfiledRawJointStrictRightPostResolveFiniteInstalledReachable A
      strategy hwin initial entry input branch state)
    (current : In₁ × In₂) (row : PairedEntryRow) :
    ProfiledRawJointStrictRightPostResolveFiniteDispatchTargetMeaning A strategy
      hwin initial entry input branch state current row := by
  rcases state with ⟨sender, receiver⟩
  rcases receiver with ⟨move, anchor, control, monitorState⟩
  have hmove := hstate.move_eq
  have hbranch := hstate.branch_eq
  dsimp only at hmove hbranch
  subst move
  subst anchor
  rcases hstate.reachable.exists_localRound_and_monitorRun
      (profiledRawJointStrictRightPostResolveFiniteMonitor A) current with
    ⟨witness, hround, hmonitor⟩
  let env : Nat → In₁ × In₂ :=
    DetParityAutomaton.omegaOfList (witness ++ [current])
  have hsafe :=
    profiledRawJointStrictRightPostResolveFiniteMove_targetMeaning A strategy
      hwin initial entry input branch env witness.length row
  have hclose := hsafe.1
  have hmeaning := hsafe.2
  dsimp only at hround hmonitor
  rw [hmonitor] at hclose
  rw [← hround] at hclose hmeaning
  constructor
  · simpa only [profiledRawJointStrictRightPostResolveFiniteDispatch] using
      hclose
  · simpa only [profiledRawJointStrictRightPostResolveFiniteDispatch] using
      hmeaning

/-! ## Concrete arbitrary-prefix dispatcher interfaces -/

/-- Every concrete process-one run state satisfies the packaged occurrence
invariant required by the dispatcher theorem. -/
theorem profiledRawJointStrictLeftPostResolveFiniteRun_installedReachable
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (branch : Bool) (past : List (In₂ × In₁)) :
    let start : LeftSenderState A × LeftReceiverState A :=
      (profiledRawJointStrictLeftPostResolveFiniteSenderInitial A strategy hwin
          initial entry input,
        profiledRawJointStrictLeftPostResolveFiniteReceiverInitial A strategy
          hwin initial entry input branch)
    ProfiledRawJointStrictLeftPostResolveFiniteInstalledReachable A strategy
      hwin initial entry input branch
        (profiledRawJointStrictLeftPostResolveFiniteRun A start past) := by
  dsimp only
  constructor
  · exact profiledRawJointStrictLeftPostResolveFiniteRun_reachable A strategy
      hwin initial entry input branch past
  · calc
      (profiledRawJointStrictLeftPostResolveFiniteRun A
          (profiledRawJointStrictLeftPostResolveFiniteSenderInitial A strategy
              hwin initial entry input,
            profiledRawJointStrictLeftPostResolveFiniteReceiverInitial A
              strategy hwin initial entry input branch) past).2.1 =
          (profiledRawJointStrictLeftPostResolveFiniteReceiverInitial A strategy
            hwin initial entry input branch).1 :=
        profiledRawJointStrictLeftPostResolveFiniteRun_move A _ past
      _ = profiledRawJointStrictLeftPostResolveFiniteMove A strategy hwin
          initial entry input := rfl
  · calc
      (profiledRawJointStrictLeftPostResolveFiniteRun A
          (profiledRawJointStrictLeftPostResolveFiniteSenderInitial A strategy
              hwin initial entry input,
            profiledRawJointStrictLeftPostResolveFiniteReceiverInitial A
              strategy hwin initial entry input branch) past).2.2.1 =
          (profiledRawJointStrictLeftPostResolveFiniteReceiverInitial A strategy
            hwin initial entry input branch).2.1 :=
        profiledRawJointStrictLeftPostResolveFiniteRun_branch A _ past
      _ = branch := rfl

/-- Mirrored concrete run states satisfy the dispatcher occurrence
invariant. -/
theorem profiledRawJointStrictRightPostResolveFiniteRun_installedReachable
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (branch : Bool) (past : List (In₁ × In₂)) :
    let start : RightSenderState A × RightReceiverState A :=
      (profiledRawJointStrictRightPostResolveFiniteSenderInitial A strategy hwin
          initial entry input,
        profiledRawJointStrictRightPostResolveFiniteReceiverInitial A strategy
          hwin initial entry input branch)
    ProfiledRawJointStrictRightPostResolveFiniteInstalledReachable A strategy
      hwin initial entry input branch
        (profiledRawJointStrictRightPostResolveFiniteRun A start past) := by
  dsimp only
  constructor
  · exact profiledRawJointStrictRightPostResolveFiniteRun_reachable A strategy
      hwin initial entry input branch past
  · calc
      (profiledRawJointStrictRightPostResolveFiniteRun A
          (profiledRawJointStrictRightPostResolveFiniteSenderInitial A strategy
              hwin initial entry input,
            profiledRawJointStrictRightPostResolveFiniteReceiverInitial A
              strategy hwin initial entry input branch) past).2.1 =
          (profiledRawJointStrictRightPostResolveFiniteReceiverInitial A strategy
            hwin initial entry input branch).1 :=
        profiledRawJointStrictRightPostResolveFiniteRun_move A _ past
      _ = profiledRawJointStrictRightPostResolveFiniteMove A strategy hwin
          initial entry input := rfl
  · calc
      (profiledRawJointStrictRightPostResolveFiniteRun A
          (profiledRawJointStrictRightPostResolveFiniteSenderInitial A strategy
              hwin initial entry input,
            profiledRawJointStrictRightPostResolveFiniteReceiverInitial A
              strategy hwin initial entry input branch) past).2.2.1 =
          (profiledRawJointStrictRightPostResolveFiniteReceiverInitial A strategy
            hwin initial entry input branch).2.1 :=
        profiledRawJointStrictRightPostResolveFiniteRun_branch A _ past
      _ = branch := rfl

/-- After any finite process-one blind prefix, dispatch returns a target with
the strict or simultaneous meaning selected at the resolving receive. -/
theorem profiledRawJointStrictLeftPostResolveFiniteRun_dispatch_targetMeaning
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (branch : Bool) (past : List (In₂ × In₁))
    (current : In₂ × In₁) (row : PairedEntryRow) :
    let start : LeftSenderState A × LeftReceiverState A :=
      (profiledRawJointStrictLeftPostResolveFiniteSenderInitial A strategy hwin
          initial entry input,
        profiledRawJointStrictLeftPostResolveFiniteReceiverInitial A strategy
          hwin initial entry input branch)
    let state := profiledRawJointStrictLeftPostResolveFiniteRun A start past
    ProfiledRawJointStrictLeftPostResolveFiniteDispatchTargetMeaning A strategy
      hwin initial entry input branch state current row := by
  dsimp only
  apply profiledRawJointStrictLeftPostResolveFiniteDispatch_targetMeaning_of_reachable
    A strategy hwin initial entry input branch
  exact profiledRawJointStrictLeftPostResolveFiniteRun_installedReachable A
    strategy hwin initial entry input branch past

/-- Mirrored arbitrary-prefix dispatch readback. -/
theorem profiledRawJointStrictRightPostResolveFiniteRun_dispatch_targetMeaning
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (branch : Bool) (past : List (In₁ × In₂))
    (current : In₁ × In₂) (row : PairedEntryRow) :
    let start : RightSenderState A × RightReceiverState A :=
      (profiledRawJointStrictRightPostResolveFiniteSenderInitial A strategy hwin
          initial entry input,
        profiledRawJointStrictRightPostResolveFiniteReceiverInitial A strategy
          hwin initial entry input branch)
    let state := profiledRawJointStrictRightPostResolveFiniteRun A start past
    ProfiledRawJointStrictRightPostResolveFiniteDispatchTargetMeaning A strategy
      hwin initial entry input branch state current row := by
  dsimp only
  apply profiledRawJointStrictRightPostResolveFiniteDispatch_targetMeaning_of_reachable
    A strategy hwin initial entry input branch
  exact profiledRawJointStrictRightPostResolveFiniteRun_installedReachable A
    strategy hwin initial entry input branch past

/-! ## Handoff to the recurrent fixed-policy carrier -/

/-- A reached process-one dispatch, whether strict or simultaneous, supplies
the existing fresh fixed-policy continuation package at its emitted target. -/
theorem
    nonempty_profiledRawJointStrictLeftPostResolveFiniteDispatchFreshPolicyPackage_of_reachable
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (branch : Bool) (state : LeftSenderState A × LeftReceiverState A)
    (hstate : ProfiledRawJointStrictLeftPostResolveFiniteInstalledReachable A
      strategy hwin initial entry input branch state)
    (current : In₂ × In₁) (row : PairedEntryRow) :
    Nonempty (ProfiledRawJointSiblingFreshPolicyPackage A strategy
      ((profiledRawJointStrictLeftPostResolveFiniteDispatch A state current.1
        current.2).receiverOutput.target row)) := by
  let certificate :=
    profiledRawJointStrictLeftPostResolveFiniteDispatch_targetMeaning_of_reachable
      A strategy hwin initial entry input branch state hstate current row
  exact
    nonempty_profiledRawJointStrictLeftPostResolveFiniteFreshPolicyPackage_of_targetMeaning
      A strategy hwin initial entry input branch
        ((profiledRawJointStrictLeftPostResolveFiniteDispatch A state current.1
          current.2).receiverOutput.target row)
        certificate.meaning state.2.2.2.2.2.1 row
        (profiledRawJointTargetRightPhysicalLetter A
          (current,
            (profiledRawJointStrictLeftPostResolveFiniteDispatch A state
              current.1 current.2).receiverOutput,
            (profiledRawJointStrictLeftPostResolveFiniteDispatch A state
              current.1 current.2).senderOutput))
        certificate.close

/-- Mirrored recurrent handoff. -/
theorem
    nonempty_profiledRawJointStrictRightPostResolveFiniteDispatchFreshPolicyPackage_of_reachable
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (branch : Bool) (state : RightSenderState A × RightReceiverState A)
    (hstate : ProfiledRawJointStrictRightPostResolveFiniteInstalledReachable A
      strategy hwin initial entry input branch state)
    (current : In₁ × In₂) (row : PairedEntryRow) :
    Nonempty (ProfiledRawJointSiblingFreshPolicyPackage A strategy
      ((profiledRawJointStrictRightPostResolveFiniteDispatch A state current.1
        current.2).receiverOutput.target row)) := by
  let certificate :=
    profiledRawJointStrictRightPostResolveFiniteDispatch_targetMeaning_of_reachable
      A strategy hwin initial entry input branch state hstate current row
  exact
    nonempty_profiledRawJointStrictRightPostResolveFiniteFreshPolicyPackage_of_targetMeaning
      A strategy hwin initial entry input branch
        ((profiledRawJointStrictRightPostResolveFiniteDispatch A state current.1
          current.2).receiverOutput.target row)
        certificate.meaning state.2.2.2.2.2.1 row
        (profiledRawJointTargetLeftPhysicalLetter A
          (current,
            (profiledRawJointStrictRightPostResolveFiniteDispatch A state
              current.1 current.2).receiverOutput,
            (profiledRawJointStrictRightPostResolveFiniteDispatch A state
              current.1 current.2).senderOutput))
        certificate.close

/-- Orientation-refined recurrent handoff for a reached process-one
dispatcher call.  Its close installs a left policy macro. -/
theorem
    nonempty_profiledRawJointStrictLeftPostResolveFiniteDispatchRightCloseFreshPolicyPackage_of_reachable
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (branch : Bool) (state : LeftSenderState A × LeftReceiverState A)
    (hstate : ProfiledRawJointStrictLeftPostResolveFiniteInstalledReachable A
      strategy hwin initial entry input branch state)
    (current : In₂ × In₁) (row : PairedEntryRow) :
    Nonempty (ProfiledRawJointRightCloseFreshPolicyPackage A strategy
      ((profiledRawJointStrictLeftPostResolveFiniteDispatch A state current.1
        current.2).receiverOutput.target row)) := by
  let certificate :=
    profiledRawJointStrictLeftPostResolveFiniteDispatch_targetMeaning_of_reachable
      A strategy hwin initial entry input branch state hstate current row
  exact
    nonempty_profiledRawJointStrictLeftPostResolveFiniteRightCloseFreshPolicyPackage_of_targetMeaning
      A strategy hwin initial entry input branch
        ((profiledRawJointStrictLeftPostResolveFiniteDispatch A state current.1
          current.2).receiverOutput.target row)
        certificate.meaning state.2.2.2.2.2.1 row
        (profiledRawJointTargetRightPhysicalLetter A
          (current,
            (profiledRawJointStrictLeftPostResolveFiniteDispatch A state
              current.1 current.2).receiverOutput,
            (profiledRawJointStrictLeftPostResolveFiniteDispatch A state
              current.1 current.2).senderOutput))
        certificate.close

/-- Mirrored reached dispatch installs a right policy macro. -/
theorem
    nonempty_profiledRawJointStrictRightPostResolveFiniteDispatchLeftCloseFreshPolicyPackage_of_reachable
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (branch : Bool) (state : RightSenderState A × RightReceiverState A)
    (hstate : ProfiledRawJointStrictRightPostResolveFiniteInstalledReachable A
      strategy hwin initial entry input branch state)
    (current : In₁ × In₂) (row : PairedEntryRow) :
    Nonempty (ProfiledRawJointLeftCloseFreshPolicyPackage A strategy
      ((profiledRawJointStrictRightPostResolveFiniteDispatch A state current.1
        current.2).receiverOutput.target row)) := by
  let certificate :=
    profiledRawJointStrictRightPostResolveFiniteDispatch_targetMeaning_of_reachable
      A strategy hwin initial entry input branch state hstate current row
  exact
    nonempty_profiledRawJointStrictRightPostResolveFiniteLeftCloseFreshPolicyPackage_of_targetMeaning
      A strategy hwin initial entry input branch
        ((profiledRawJointStrictRightPostResolveFiniteDispatch A state current.1
          current.2).receiverOutput.target row)
        certificate.meaning state.2.2.2.2.2.1 row
        (profiledRawJointTargetLeftPhysicalLetter A
          (current,
            (profiledRawJointStrictRightPostResolveFiniteDispatch A state
              current.1 current.2).receiverOutput,
            (profiledRawJointStrictRightPostResolveFiniteDispatch A state
              current.1 current.2).senderOutput))
        certificate.close

/-- Concrete arbitrary-prefix process-one handoff. -/
theorem
    nonempty_profiledRawJointStrictLeftPostResolveFiniteRun_dispatchFreshPolicyPackage
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (branch : Bool) (past : List (In₂ × In₁))
    (current : In₂ × In₁) (row : PairedEntryRow) :
    let start : LeftSenderState A × LeftReceiverState A :=
      (profiledRawJointStrictLeftPostResolveFiniteSenderInitial A strategy hwin
          initial entry input,
        profiledRawJointStrictLeftPostResolveFiniteReceiverInitial A strategy
          hwin initial entry input branch)
    let state := profiledRawJointStrictLeftPostResolveFiniteRun A start past
    Nonempty (ProfiledRawJointSiblingFreshPolicyPackage A strategy
      ((profiledRawJointStrictLeftPostResolveFiniteDispatch A state current.1
        current.2).receiverOutput.target row)) := by
  dsimp only
  apply
    nonempty_profiledRawJointStrictLeftPostResolveFiniteDispatchFreshPolicyPackage_of_reachable
      A strategy hwin initial entry input branch
  exact profiledRawJointStrictLeftPostResolveFiniteRun_installedReachable A
    strategy hwin initial entry input branch past

/-- Concrete arbitrary-prefix mirrored handoff. -/
theorem
    nonempty_profiledRawJointStrictRightPostResolveFiniteRun_dispatchFreshPolicyPackage
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (branch : Bool) (past : List (In₁ × In₂))
    (current : In₁ × In₂) (row : PairedEntryRow) :
    let start : RightSenderState A × RightReceiverState A :=
      (profiledRawJointStrictRightPostResolveFiniteSenderInitial A strategy hwin
          initial entry input,
        profiledRawJointStrictRightPostResolveFiniteReceiverInitial A strategy
          hwin initial entry input branch)
    let state := profiledRawJointStrictRightPostResolveFiniteRun A start past
    Nonempty (ProfiledRawJointSiblingFreshPolicyPackage A strategy
      ((profiledRawJointStrictRightPostResolveFiniteDispatch A state current.1
        current.2).receiverOutput.target row)) := by
  dsimp only
  apply
    nonempty_profiledRawJointStrictRightPostResolveFiniteDispatchFreshPolicyPackage_of_reachable
      A strategy hwin initial entry input branch
  exact profiledRawJointStrictRightPostResolveFiniteRun_installedReachable A
    strategy hwin initial entry input branch past

end

end DetParityAutomaton

end DistributedSynthesis
