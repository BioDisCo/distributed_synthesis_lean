/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridInitialOneRoundReplacement
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointGuardedFirstPolicyRootHandoff
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointUnitPolicyLeaderFreeKernel

/-!
# Exact children below the ambiguous initial first block

The root-pinned first block below an ambiguous initial receive is indexed by
the literal first input pair.  Its selected semantic source is therefore not
definitionally the source selected at an arbitrary reachable hybrid common
control, even when the two finite incidence codes happen to agree.

This file retains the honest dependent index.  A child tag consists of the
finite first input pair and one literal child emitted by that pair's exact
right- or left-block controller.  From that tag we recover the literal child
source, its fresh ordinary one-sided policy, and the complete recurrent
controller bank.  The outer orientation tag is construction provenance only;
it is not stored or inspected as a graph or strict-leader signal by a local
transition.
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

/-! ## Finite dependent child code -/

/-- The exact source selected for the initial right-block controller rooted
at `first`. -/
abbrev ProfiledRawJointHybridInitialExactRightSelectedSource
    (first : In₁ × In₂) :=
  profiledRawJointRootPinnedSelectedSource A strategy
    (ProfiledRawJointHybridInitialImmediateRightSource A strategy first)
    (profiledRawJointHybridInitialImmediateRightRootPredicate A strategy first)
    (profiledRawJointHybridInitialImmediateRightPolicy A strategy hwin first)

/-- Initial left-block mirror. -/
abbrev ProfiledRawJointHybridInitialExactLeftSelectedSource
    (first : In₁ × In₂) :=
  profiledRawJointRootPinnedSelectedSource A strategy
    (ProfiledRawJointHybridInitialImmediateLeftSource A strategy first)
    (profiledRawJointHybridInitialImmediateLeftRootPredicate A strategy first)
    (profiledRawJointHybridInitialImmediateLeftPolicy A strategy hwin first)

/-- A literal child emitted by one exact initial right-block controller,
retaining the finite root-pair index on which its type depends. -/
abbrev ProfiledRawJointHybridInitialExactRightTaggedChild :=
  Σ first : In₁ × In₂,
    ProfiledRawJointOneSidedLiteralChildCode A strategy
      (ProfiledRawJointHybridInitialExactRightSelectedSource A strategy hwin
        first)

/-- Exact initial left-block child summand. -/
abbrev ProfiledRawJointHybridInitialExactLeftTaggedChild :=
  Σ first : In₁ × In₂,
    ProfiledRawJointOneSidedLiteralChildCode A strategy
      (ProfiledRawJointHybridInitialExactLeftSelectedSource A strategy hwin
        first)

/-- The finite exact-child code at the close of either initial exceptional
orientation. -/
abbrev ProfiledRawJointHybridInitialExactTaggedChildCode :=
  ProfiledRawJointHybridInitialExactRightTaggedChild A strategy hwin ⊕
    ProfiledRawJointHybridInitialExactLeftTaggedChild A strategy hwin

noncomputable instance
    profiledRawJointHybridInitialExactTaggedChildCodeFintype :
    Fintype
      (ProfiledRawJointHybridInitialExactTaggedChildCode A strategy hwin) := by
  classical
  infer_instance

/-! ## Exact source, policy, and recurrent bank -/

/-- Recover the literal semantic child represented by an initial-exact tag. -/
noncomputable def profiledRawJointHybridInitialExactTaggedChildSource
    (child : ProfiledRawJointHybridInitialExactTaggedChildCode A strategy hwin) :
    ProfiledRawJointOneSidedSemanticState A strategy (I := Unit) :=
  match child with
  | .inl child =>
      profiledRawJointOneSidedLiteralChildSource A strategy
        (ProfiledRawJointHybridInitialExactRightSelectedSource A strategy hwin
          child.1) child.2
  | .inr child =>
      profiledRawJointOneSidedLiteralChildSource A strategy
        (ProfiledRawJointHybridInitialExactLeftSelectedSource A strategy hwin
          child.1) child.2

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Source recovery preserves the literal incidence code in the dependent
tag. -/
theorem profiledRawJointHybridInitialExactTaggedChildSource_code
    (child : ProfiledRawJointHybridInitialExactTaggedChildCode A strategy hwin) :
    (profiledRawJointHybridInitialExactTaggedChildSource A strategy hwin child
      ).code A =
      match child with
      | .inl child => child.2.1
      | .inr child => child.2.1 := by
  cases child with
  | inl child =>
      exact profiledRawJointOneSidedLiteralChildSource_code A strategy
        (ProfiledRawJointHybridInitialExactRightSelectedSource A strategy hwin
          child.1) child.2
  | inr child =>
      exact profiledRawJointOneSidedLiteralChildSource_code A strategy
        (ProfiledRawJointHybridInitialExactLeftSelectedSource A strategy hwin
          child.1) child.2

/-- Recover the fresh fixed one-sided policy selected for this literal
child. -/
noncomputable def profiledRawJointHybridInitialExactTaggedChildPolicy
    (child : ProfiledRawJointHybridInitialExactTaggedChildCode A strategy hwin) :
    ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      ((profiledRawJointHybridInitialExactTaggedChildSource A strategy hwin
        child).code A) := by
  cases child with
  | inl child =>
      let policy :=
        profiledRawJointRootPinnedLiteralChildPolicyBank A strategy hwin
          (ProfiledRawJointHybridInitialImmediateRightSource A strategy
            child.1)
          (profiledRawJointHybridInitialImmediateRightRootPredicate A strategy
            child.1)
          (profiledRawJointHybridInitialImmediateRightPolicy A strategy hwin
            child.1) child.2
      simpa only [profiledRawJointHybridInitialExactTaggedChildSource,
        profiledRawJointOneSidedLiteralChildSource_code] using policy
  | inr child =>
      let policy :=
        profiledRawJointRootPinnedLiteralChildPolicyBank A strategy hwin
          (ProfiledRawJointHybridInitialImmediateLeftSource A strategy child.1)
          (profiledRawJointHybridInitialImmediateLeftRootPredicate A strategy
            child.1)
          (profiledRawJointHybridInitialImmediateLeftPolicy A strategy hwin
            child.1) child.2
      simpa only [profiledRawJointHybridInitialExactTaggedChildSource,
        profiledRawJointOneSidedLiteralChildSource_code] using policy

/-- Complete ordinary recurrent controller bank below the exact initial
child. -/
noncomputable def
    profiledRawJointHybridInitialExactTaggedChildControllerBank
    (child : ProfiledRawJointHybridInitialExactTaggedChildCode A strategy hwin) :
    ProfiledRawJointUnitPolicyControllerBank A strategy
      (profiledRawJointHybridInitialExactTaggedChildSource A strategy hwin
        child)
      (profiledRawJointHybridInitialExactTaggedChildPolicy A strategy hwin
        child) :=
  profiledRawJointUnitPolicyControllerBank A strategy
    (profiledRawJointHybridInitialExactTaggedChildSource A strategy hwin child)
    (profiledRawJointHybridInitialExactTaggedChildPolicy A strategy hwin child)

/-! ## Dependent recurrent local-control families -/

abbrev ProfiledRawJointHybridInitialExactTaggedRightOwner
    (child : ProfiledRawJointHybridInitialExactTaggedChildCode A strategy hwin) :=
  ProfiledRawJointUnitPolicyRightOwner A strategy
    (profiledRawJointHybridInitialExactTaggedChildSource A strategy hwin child)
    (profiledRawJointHybridInitialExactTaggedChildPolicy A strategy hwin child)
    (profiledRawJointHybridInitialExactTaggedChildControllerBank A strategy hwin
      child) ()

abbrev ProfiledRawJointHybridInitialExactTaggedLeftReceiver
    (child : ProfiledRawJointHybridInitialExactTaggedChildCode A strategy hwin) :=
  ProfiledRawJointUnitPolicyLeftReceiver A strategy
    (profiledRawJointHybridInitialExactTaggedChildSource A strategy hwin child)
    (profiledRawJointHybridInitialExactTaggedChildPolicy A strategy hwin child)
    ()

abbrev ProfiledRawJointHybridInitialExactTaggedRightReceiver
    (child : ProfiledRawJointHybridInitialExactTaggedChildCode A strategy hwin) :=
  ProfiledRawJointUnitPolicyRightReceiver A strategy
    (profiledRawJointHybridInitialExactTaggedChildSource A strategy hwin child)
    (profiledRawJointHybridInitialExactTaggedChildPolicy A strategy hwin child)
    ()

abbrev ProfiledRawJointHybridInitialExactTaggedLeftOwner
    (child : ProfiledRawJointHybridInitialExactTaggedChildCode A strategy hwin) :=
  ProfiledRawJointUnitPolicyLeftOwner A strategy
    (profiledRawJointHybridInitialExactTaggedChildSource A strategy hwin child)
    (profiledRawJointHybridInitialExactTaggedChildPolicy A strategy hwin child)
    (profiledRawJointHybridInitialExactTaggedChildControllerBank A strategy hwin
      child) ()

noncomputable instance
    profiledRawJointHybridInitialExactTaggedRightOwnerFintype
    (child : ProfiledRawJointHybridInitialExactTaggedChildCode A strategy hwin) :
    Fintype
      (ProfiledRawJointHybridInitialExactTaggedRightOwner A strategy hwin
        child) := by
  classical
  infer_instance

noncomputable instance
    profiledRawJointHybridInitialExactTaggedLeftReceiverFintype
    (child : ProfiledRawJointHybridInitialExactTaggedChildCode A strategy hwin) :
    Fintype
      (ProfiledRawJointHybridInitialExactTaggedLeftReceiver A strategy hwin
        child) := by
  classical
  infer_instance

noncomputable instance
    profiledRawJointHybridInitialExactTaggedRightReceiverFintype
    (child : ProfiledRawJointHybridInitialExactTaggedChildCode A strategy hwin) :
    Fintype
      (ProfiledRawJointHybridInitialExactTaggedRightReceiver A strategy hwin
        child) := by
  classical
  infer_instance

noncomputable instance
    profiledRawJointHybridInitialExactTaggedLeftOwnerFintype
    (child : ProfiledRawJointHybridInitialExactTaggedChildCode A strategy hwin) :
    Fintype
      (ProfiledRawJointHybridInitialExactTaggedLeftOwner A strategy hwin
        child) := by
  classical
  infer_instance

/-! ## Concrete close tags -/

/-- Package the literal target emitted by an exact initial right-block
receiver. -/
def profiledRawJointHybridInitialExactRightTaggedTarget
    (first : In₁ × In₂) (row : PairedEntryRow)
    (past : List (In₂ × In₁)) (input : In₂ × In₁) :
    ProfiledRawJointHybridInitialExactTaggedChildCode A strategy hwin :=
  .inl ⟨first,
    profiledRawJointGuardedFirstRightTarget A strategy
      (ProfiledRawJointHybridInitialImmediateRightSource A strategy first)
      (profiledRawJointHybridInitialImmediateRightRootPredicate A strategy
        first)
      (profiledRawJointHybridInitialImmediateRightPolicy A strategy hwin first)
      row past input⟩

/-- Exact initial left-block close mirror. -/
def profiledRawJointHybridInitialExactLeftTaggedTarget
    (first : In₁ × In₂) (row : PairedEntryRow)
    (past : List (In₁ × In₂)) (input : In₁ × In₂) :
    ProfiledRawJointHybridInitialExactTaggedChildCode A strategy hwin :=
  .inr ⟨first,
    profiledRawJointGuardedFirstLeftTarget A strategy
      (ProfiledRawJointHybridInitialImmediateLeftSource A strategy first)
      (profiledRawJointHybridInitialImmediateLeftRootPredicate A strategy first)
      (profiledRawJointHybridInitialImmediateLeftPolicy A strategy hwin first)
      row past input⟩

/-- The exact recurrent child currently staged in a right receiver control. -/
def profiledRawJointHybridInitialImmediateRightReceiverChildTag
    (receiver : ProfiledRawJointHybridInitialImmediateRightReceiver A strategy
      hwin) :
    ProfiledRawJointHybridInitialExactTaggedChildCode A strategy hwin :=
  .inl ⟨receiver.first, receiver.stage.child⟩

/-- Left receiver mirror. -/
def profiledRawJointHybridInitialImmediateLeftReceiverChildTag
    (receiver : ProfiledRawJointHybridInitialImmediateLeftReceiver A strategy
      hwin) :
    ProfiledRawJointHybridInitialExactTaggedChildCode A strategy hwin :=
  .inr ⟨receiver.first, receiver.stage.child⟩

/-- Tag the target actually stored in the narrowed right controller's root
record.  The following theorem identifies it with the semantic exact target;
the definition itself remains directly executable from the finite table. -/
noncomputable def profiledRawJointHybridInitialExactRightControllerRootTarget
    (first : In₁ × In₂) (row : PairedEntryRow) (input : In₂ × In₁) :
    ProfiledRawJointHybridInitialExactTaggedChildCode A strategy hwin :=
  let monitor :=
    profiledRawJointHybridInitialImmediateRightMonitor A strategy hwin first
  let controller :=
    profiledRawJointHybridInitialImmediateRightController A strategy hwin first
  let record := narrowedRecord monitor (controller.labeledTree [])
    monitor.initial input
  .inl ⟨first, record.2.1.target row⟩

/-- Left-controller root target mirror. -/
noncomputable def profiledRawJointHybridInitialExactLeftControllerRootTarget
    (first : In₁ × In₂) (row : PairedEntryRow) (input : In₁ × In₂) :
    ProfiledRawJointHybridInitialExactTaggedChildCode A strategy hwin :=
  let monitor :=
    profiledRawJointHybridInitialImmediateLeftMonitor A strategy hwin first
  let controller :=
    profiledRawJointHybridInitialImmediateLeftController A strategy hwin first
  let record := narrowedRecord monitor (controller.labeledTree [])
    monitor.initial input
  .inr ⟨first, record.2.1.target row⟩

theorem profiledRawJointHybridInitialExactRightControllerRootTarget_eq
    (first : In₁ × In₂) (row : PairedEntryRow) (input : In₂ × In₁) :
    profiledRawJointHybridInitialExactRightControllerRootTarget A strategy hwin
        first row input =
      profiledRawJointHybridInitialExactRightTaggedTarget A strategy hwin first
        row [] input := by
  rw [profiledRawJointHybridInitialExactRightControllerRootTarget,
    profiledRawJointHybridInitialImmediateRightController_rootRecord A
      strategy hwin]
  rfl

theorem profiledRawJointHybridInitialExactLeftControllerRootTarget_eq
    (first : In₁ × In₂) (row : PairedEntryRow) (input : In₁ × In₂) :
    profiledRawJointHybridInitialExactLeftControllerRootTarget A strategy hwin
        first row input =
      profiledRawJointHybridInitialExactLeftTaggedTarget A strategy hwin first
        row [] input := by
  rw [profiledRawJointHybridInitialExactLeftControllerRootTarget,
    profiledRawJointHybridInitialImmediateLeftController_rootRecord A strategy
      hwin]
  rfl

variable
  (controllers : ProfiledRawJointRootCompatibleInitialControllers A strategy)

/-- The initial right receiver stages exactly the narrowed root target. -/
@[simp] theorem
    profiledRawJointHybridInitialOneShadowRecvTwo_childTag
    (shadow : ProfiledRawJointHybridInitialOneShadow A strategy hwin
      controllers)
    (row : PairedEntryRow) (ownInput : In₂) (deliveredInput : In₁) :
    profiledRawJointHybridInitialImmediateRightReceiverChildTag A strategy hwin
        (profiledRawJointHybridInitialOneShadowRecvTwo A strategy hwin
          controllers shadow row ownInput deliveredInput).2 =
      profiledRawJointHybridInitialExactRightControllerRootTarget A strategy
        hwin shadow.common.1 row (ownInput, deliveredInput) := by
  change
    profiledRawJointHybridInitialExactRightTaggedTarget A strategy hwin
        shadow.common.1 row [] (ownInput, deliveredInput) = _
  exact
    (profiledRawJointHybridInitialExactRightControllerRootTarget_eq A strategy
      hwin shadow.common.1 row (ownInput, deliveredInput)).symm

/-- Initial left receiver mirror. -/
@[simp] theorem
    profiledRawJointHybridInitialTwoShadowRecvOne_childTag
    (shadow : ProfiledRawJointHybridInitialTwoShadow A strategy hwin
      controllers)
    (row : PairedEntryRow) (ownInput : In₁) (deliveredInput : In₂) :
    profiledRawJointHybridInitialImmediateLeftReceiverChildTag A strategy hwin
        (profiledRawJointHybridInitialTwoShadowRecvOne A strategy hwin
          controllers shadow row ownInput deliveredInput).2 =
      profiledRawJointHybridInitialExactLeftControllerRootTarget A strategy hwin
        shadow.common.1 row (ownInput, deliveredInput) := by
  change
    profiledRawJointHybridInitialExactLeftTaggedTarget A strategy hwin
        shadow.common.1 row [] (ownInput, deliveredInput) = _
  exact
    (profiledRawJointHybridInitialExactLeftControllerRootTarget_eq A strategy
      hwin shadow.common.1 row (ownInput, deliveredInput)).symm

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
@[simp] theorem
    profiledRawJointHybridInitialExactTaggedChildSource_rightTarget
    (first : In₁ × In₂) (row : PairedEntryRow)
    (past : List (In₂ × In₁)) (input : In₂ × In₁) :
    profiledRawJointHybridInitialExactTaggedChildSource A strategy hwin
        (profiledRawJointHybridInitialExactRightTaggedTarget A strategy hwin
          first row past input) =
      profiledRawJointOneSidedLiteralChildSource A strategy
        (ProfiledRawJointHybridInitialExactRightSelectedSource A strategy hwin
          first)
        (profiledRawJointGuardedFirstRightTarget A strategy
          (ProfiledRawJointHybridInitialImmediateRightSource A strategy first)
          (profiledRawJointHybridInitialImmediateRightRootPredicate A strategy
            first)
          (profiledRawJointHybridInitialImmediateRightPolicy A strategy hwin
            first) row past input) :=
  rfl

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
@[simp] theorem
    profiledRawJointHybridInitialExactTaggedChildSource_leftTarget
    (first : In₁ × In₂) (row : PairedEntryRow)
    (past : List (In₁ × In₂)) (input : In₁ × In₂) :
    profiledRawJointHybridInitialExactTaggedChildSource A strategy hwin
        (profiledRawJointHybridInitialExactLeftTaggedTarget A strategy hwin
          first row past input) =
      profiledRawJointOneSidedLiteralChildSource A strategy
        (ProfiledRawJointHybridInitialExactLeftSelectedSource A strategy hwin
          first)
        (profiledRawJointGuardedFirstLeftTarget A strategy
          (ProfiledRawJointHybridInitialImmediateLeftSource A strategy first)
          (profiledRawJointHybridInitialImmediateLeftRootPredicate A strategy
            first)
          (profiledRawJointHybridInitialImmediateLeftPolicy A strategy hwin
            first) row past input) :=
  rfl

/-! ## The ambiguous local entry is the exact controller root -/

variable
  (controllers : ProfiledRawJointRootCompatibleInitialControllers A strategy)

/-- At an ambiguous process-one shadow, the independent `noRecv` and receive
tables emit the two physical projections of the exact pinned right root. -/
theorem profiledRawJointHybridInitialImmediateRight_localOutputs_eq_exactRoot
    (shadow : ProfiledRawJointHybridInitialOneShadow A strategy hwin
      controllers)
    (row : PairedEntryRow) (current : In₁ × In₂) :
    ((profiledRawJointHybridInitialOneShadowNoRecv A strategy hwin controllers
        shadow current.1).1,
      (profiledRawJointHybridInitialOneShadowRecvTwo A strategy hwin
        controllers shadow row current.2 current.1).1) =
      let first := shadow.common.1
      let record :=
        profiledRawJointHybridInitialImmediateRightRootRecord A strategy hwin
          first (current.2, current.1)
      (record.2.2, pairedRightInformedForRow row record.2.1.physical) := by
  rw [profiledRawJointHybridInitialImmediateRight_localOutputs A strategy hwin
    controllers]
  dsimp only
  rw [profiledRawJointHybridInitialImmediateRightController_rootRecord A
    strategy hwin]

/-- Process-two/left mirror. -/
theorem profiledRawJointHybridInitialImmediateLeft_localOutputs_eq_exactRoot
    (shadow : ProfiledRawJointHybridInitialTwoShadow A strategy hwin
      controllers)
    (row : PairedEntryRow) (current : In₁ × In₂) :
    ((profiledRawJointHybridInitialTwoShadowRecvOne A strategy hwin controllers
        shadow row current.1 current.2).1,
      (profiledRawJointHybridInitialTwoShadowNoRecv A strategy hwin controllers
        shadow current.2).1) =
      let first := shadow.common.1
      let record :=
        profiledRawJointHybridInitialImmediateLeftRootRecord A strategy hwin
          first current
      (pairedLeftInformedForRow row record.2.1.physical, record.2.2) := by
  rw [profiledRawJointHybridInitialImmediateLeft_localOutputs A strategy hwin
    controllers]
  dsimp only
  rw [profiledRawJointHybridInitialImmediateLeftController_rootRecord A
    strategy hwin]

/-! ## Ordinary roots reached at an exact close -/

/-- Any staged right-block child initializes the ordinary left-policy macro
at its exact stored slot.  This is the runtime close interface; unlike the
semantic specialization below, it works for every target emitted by the
narrowed controller whose active-slot witness was retained locally. -/
noncomputable def profiledRawJointHybridInitialExactRightStageChildRootMacro
    (first : In₁ × In₂)
    (stage : ProfiledRawJointHybridInitialImmediateRightStageAt A strategy hwin
      first) :
    let child : ProfiledRawJointHybridInitialExactTaggedChildCode A strategy
      hwin := .inl ⟨first, stage.child⟩
    ProfiledRawJointUnitLeftPolicyMacro A strategy
      ((profiledRawJointHybridInitialExactTaggedChildSource A strategy hwin
        child).code A)
      (profiledRawJointHybridInitialExactTaggedChildPolicy A strategy hwin
        child) := by
  let child : ProfiledRawJointHybridInitialExactTaggedChildCode A strategy
    hwin := .inl ⟨first, stage.child⟩
  let policy :=
    profiledRawJointHybridInitialExactTaggedChildPolicy A strategy hwin child
  have hsource :
      (profiledRawJointHybridInitialExactTaggedChildSource A strategy hwin child
        ).code A = stage.child.1 := by
    exact profiledRawJointHybridInitialExactTaggedChildSource_code A strategy
      hwin child
  have hrootCode :
      (policy.run []).1 =
        (profiledRawJointHybridInitialExactTaggedChildSource A strategy hwin
          child).code A := by
    have hroot := congrArg Prod.fst policy.accepts.1.1
    simpa [sourceFreeBeliefCodeParityRunAutomaton] using hroot
  exact {
    state := policy.run []
    reachable := ⟨[], rfl⟩
    slot := stage.slot
    active_slot := by
      rw [hrootCode, hsource]
      exact stage.active_slot }

/-- Staged left-block close mirror. -/
noncomputable def profiledRawJointHybridInitialExactLeftStageChildRootMacro
    (first : In₁ × In₂)
    (stage : ProfiledRawJointHybridInitialImmediateLeftStageAt A strategy hwin
      first) :
    let child : ProfiledRawJointHybridInitialExactTaggedChildCode A strategy
      hwin := .inr ⟨first, stage.child⟩
    ProfiledRawJointUnitRightPolicyMacro A strategy
      ((profiledRawJointHybridInitialExactTaggedChildSource A strategy hwin
        child).code A)
      (profiledRawJointHybridInitialExactTaggedChildPolicy A strategy hwin
        child) := by
  let child : ProfiledRawJointHybridInitialExactTaggedChildCode A strategy
    hwin := .inr ⟨first, stage.child⟩
  let policy :=
    profiledRawJointHybridInitialExactTaggedChildPolicy A strategy hwin child
  have hsource :
      (profiledRawJointHybridInitialExactTaggedChildSource A strategy hwin child
        ).code A = stage.child.1 := by
    exact profiledRawJointHybridInitialExactTaggedChildSource_code A strategy
      hwin child
  have hrootCode :
      (policy.run []).1 =
        (profiledRawJointHybridInitialExactTaggedChildSource A strategy hwin
          child).code A := by
    have hroot := congrArg Prod.fst policy.accepts.1.1
    simpa [sourceFreeBeliefCodeParityRunAutomaton] using hroot
  exact {
    state := policy.run []
    reachable := ⟨[], rfl⟩
    slot := stage.slot
    active_slot := by
      rw [hrootCode, hsource]
      exact stage.active_slot }

/-- Runtime right receiver close: its staged tag and staged root macro share
one dependent child index. -/
noncomputable def
    profiledRawJointHybridInitialImmediateRightReceiverChildRootMacro
    (receiver : ProfiledRawJointHybridInitialImmediateRightReceiver A strategy
      hwin) :
    let child :=
      profiledRawJointHybridInitialImmediateRightReceiverChildTag A strategy
        hwin receiver
    ProfiledRawJointUnitLeftPolicyMacro A strategy
      ((profiledRawJointHybridInitialExactTaggedChildSource A strategy hwin
        child).code A)
      (profiledRawJointHybridInitialExactTaggedChildPolicy A strategy hwin
        child) :=
  profiledRawJointHybridInitialExactRightStageChildRootMacro A strategy hwin
    receiver.first receiver.stage

/-- Runtime left receiver close mirror. -/
noncomputable def
    profiledRawJointHybridInitialImmediateLeftReceiverChildRootMacro
    (receiver : ProfiledRawJointHybridInitialImmediateLeftReceiver A strategy
      hwin) :
    let child :=
      profiledRawJointHybridInitialImmediateLeftReceiverChildTag A strategy hwin
        receiver
    ProfiledRawJointUnitRightPolicyMacro A strategy
      ((profiledRawJointHybridInitialExactTaggedChildSource A strategy hwin
        child).code A)
      (profiledRawJointHybridInitialExactTaggedChildPolicy A strategy hwin
        child) :=
  profiledRawJointHybridInitialExactLeftStageChildRootMacro A strategy hwin
    receiver.first receiver.stage

omit [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem
    profiledRawJointHybridInitialImmediateRightReceiverChildRootMacro_state
    (receiver : ProfiledRawJointHybridInitialImmediateRightReceiver A strategy
      hwin) :
    (profiledRawJointHybridInitialImmediateRightReceiverChildRootMacro A
      strategy hwin receiver).state =
      (profiledRawJointHybridInitialExactTaggedChildPolicy A strategy hwin
        (profiledRawJointHybridInitialImmediateRightReceiverChildTag A strategy
          hwin receiver)).run [] :=
  rfl

omit [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem
    profiledRawJointHybridInitialImmediateLeftReceiverChildRootMacro_state
    (receiver : ProfiledRawJointHybridInitialImmediateLeftReceiver A strategy
      hwin) :
    (profiledRawJointHybridInitialImmediateLeftReceiverChildRootMacro A strategy
      hwin receiver).state =
      (profiledRawJointHybridInitialExactTaggedChildPolicy A strategy hwin
        (profiledRawJointHybridInitialImmediateLeftReceiverChildTag A strategy
          hwin receiver)).run [] :=
  rfl

/-- The exact right close initializes the ordinary left-policy macro of its
literal child. -/
noncomputable def
    profiledRawJointHybridInitialExactRightTaggedChildRootMacro
    (first : In₁ × In₂) (row : PairedEntryRow)
    (past : List (In₂ × In₁)) (input : In₂ × In₁) :
    let child :=
      profiledRawJointHybridInitialExactRightTaggedTarget A strategy hwin first
        row past input
    ProfiledRawJointUnitLeftPolicyMacro A strategy
      ((profiledRawJointHybridInitialExactTaggedChildSource A strategy hwin
        child).code A)
      (profiledRawJointHybridInitialExactTaggedChildPolicy A strategy hwin
        child) := by
  let literal := profiledRawJointGuardedFirstRightTarget A strategy
    (ProfiledRawJointHybridInitialImmediateRightSource A strategy first)
    (profiledRawJointHybridInitialImmediateRightRootPredicate A strategy first)
    (profiledRawJointHybridInitialImmediateRightPolicy A strategy hwin first)
    row past input
  let child := profiledRawJointHybridInitialExactRightTaggedTarget A strategy
    hwin first row past input
  let policy :=
    profiledRawJointHybridInitialExactTaggedChildPolicy A strategy hwin child
  let activation :=
    profiledRawJointHybridInitialImmediateRightActivation A strategy hwin first
  let slot := profiledRawRightChildSlot A
    ((profiledRawJointInitialCommonBaseWorld A strategy first.1 first.2
      ).procOneSlot A) activation.lambda row past input
  have hliteral : literal.1.family.left () = some slot := by
    exact activation.target_active_slot row past input
  have hsource :
      (profiledRawJointHybridInitialExactTaggedChildSource A strategy hwin child
        ).code A = literal.1 := by
    exact profiledRawJointHybridInitialExactTaggedChildSource_code A strategy
      hwin child
  have hrootCode :
      (policy.run []).1 =
        (profiledRawJointHybridInitialExactTaggedChildSource A strategy hwin
          child).code A := by
    have hroot := congrArg Prod.fst policy.accepts.1.1
    simpa [sourceFreeBeliefCodeParityRunAutomaton] using hroot
  exact {
    state := policy.run []
    reachable := ⟨[], rfl⟩
    slot := slot
    active_slot := by
      rw [hrootCode, hsource]
      exact hliteral }

/-- Left-close mirror. -/
noncomputable def
    profiledRawJointHybridInitialExactLeftTaggedChildRootMacro
    (first : In₁ × In₂) (row : PairedEntryRow)
    (past : List (In₁ × In₂)) (input : In₁ × In₂) :
    let child :=
      profiledRawJointHybridInitialExactLeftTaggedTarget A strategy hwin first
        row past input
    ProfiledRawJointUnitRightPolicyMacro A strategy
      ((profiledRawJointHybridInitialExactTaggedChildSource A strategy hwin
        child).code A)
      (profiledRawJointHybridInitialExactTaggedChildPolicy A strategy hwin
        child) := by
  let literal := profiledRawJointGuardedFirstLeftTarget A strategy
    (ProfiledRawJointHybridInitialImmediateLeftSource A strategy first)
    (profiledRawJointHybridInitialImmediateLeftRootPredicate A strategy first)
    (profiledRawJointHybridInitialImmediateLeftPolicy A strategy hwin first)
    row past input
  let child := profiledRawJointHybridInitialExactLeftTaggedTarget A strategy
    hwin first row past input
  let policy :=
    profiledRawJointHybridInitialExactTaggedChildPolicy A strategy hwin child
  let activation :=
    profiledRawJointHybridInitialImmediateLeftActivation A strategy hwin first
  let slot := profiledRawLeftChildSlot A
    ((profiledRawJointInitialCommonBaseWorld A strategy first.1 first.2
      ).procTwoSlot A) activation.lambda row past input
  have hliteral : literal.1.family.right () = some slot := by
    exact activation.target_active_slot row past input
  have hsource :
      (profiledRawJointHybridInitialExactTaggedChildSource A strategy hwin child
        ).code A = literal.1 := by
    exact profiledRawJointHybridInitialExactTaggedChildSource_code A strategy
      hwin child
  have hrootCode :
      (policy.run []).1 =
        (profiledRawJointHybridInitialExactTaggedChildSource A strategy hwin
          child).code A := by
    have hroot := congrArg Prod.fst policy.accepts.1.1
    simpa [sourceFreeBeliefCodeParityRunAutomaton] using hroot
  exact {
    state := policy.run []
    reachable := ⟨[], rfl⟩
    slot := slot
    active_slot := by
      rw [hrootCode, hsource]
      exact hliteral }

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
@[simp] theorem
    profiledRawJointHybridInitialExactRightTaggedChildRootMacro_state
    (first : In₁ × In₂) (row : PairedEntryRow)
    (past : List (In₂ × In₁)) (input : In₂ × In₁) :
    (profiledRawJointHybridInitialExactRightTaggedChildRootMacro A strategy hwin
      first row past input).state =
      (profiledRawJointHybridInitialExactTaggedChildPolicy A strategy hwin
        (profiledRawJointHybridInitialExactRightTaggedTarget A strategy hwin
          first row past input)).run [] :=
  rfl

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
@[simp] theorem
    profiledRawJointHybridInitialExactLeftTaggedChildRootMacro_state
    (first : In₁ × In₂) (row : PairedEntryRow)
    (past : List (In₁ × In₂)) (input : In₁ × In₂) :
    (profiledRawJointHybridInitialExactLeftTaggedChildRootMacro A strategy hwin
      first row past input).state =
      (profiledRawJointHybridInitialExactTaggedChildPolicy A strategy hwin
        (profiledRawJointHybridInitialExactLeftTaggedTarget A strategy hwin
          first row past input)).run [] :=
  rfl

end

end DetParityAutomaton

end DistributedSynthesis
