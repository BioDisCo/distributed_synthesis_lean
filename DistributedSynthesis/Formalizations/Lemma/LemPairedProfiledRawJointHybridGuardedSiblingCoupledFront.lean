/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridMegaGuardedTargetReachability

/-!
# Coupled root-pinned front for guarded sibling blocks

At a locally ambiguous simultaneous/strict boundary, each process retains the
finite guarded sibling owner belonging to one common installation.  A genuine
simultaneous receive advances the exact root-pinned common control and resets
the two guarded owners below its successor.  A strict round instead exposes
the corresponding owner/receiver pair and thereafter runs one finite guarded
sibling table until its checked target is installed.

All states below are finite and all transition functions inspect only local
controls, delivered controls, and input letters.  The graph case is supplied
by the surrounding communication semantics, not stored in a local state.
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

private abbrev Installation :=
  ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin

/-! ## Ambiguous common/strict controls -/

/-- Process one retains the guarded-right sender below the current common
installation while the next communication graph is still unknown. -/
abbrev ProfiledRawJointHybridGuardedCoupledOne :=
  ProfiledRawJointHybridGuardedRightInstalledOwner A strategy hwin

/-- Process two retains the guarded-left sender at the same installation. -/
abbrev ProfiledRawJointHybridGuardedCoupledTwo :=
  ProfiledRawJointHybridGuardedLeftInstalledOwner A strategy hwin

noncomputable def initialProfiledRawJointHybridGuardedCoupledOne
    (installation : Installation A strategy hwin) :
    ProfiledRawJointHybridGuardedCoupledOne A strategy hwin :=
  let move := profiledRawJointHybridGuardedRightMoveAt A strategy hwin
    installation
  ⟨installation, (move.memberController A false).initial⟩

noncomputable def initialProfiledRawJointHybridGuardedCoupledTwo
    (installation : Installation A strategy hwin) :
    ProfiledRawJointHybridGuardedCoupledTwo A strategy hwin :=
  let move := profiledRawJointHybridGuardedLeftMoveAt A strategy hwin
    installation
  ⟨installation, (move.memberController A false).initial⟩

/-! ## Repeated simultaneous rounds -/

/-- Process-one projection of one genuine simultaneous round. -/
noncomputable def stepProfiledRawJointHybridGuardedCoupledBothOne
    (state : ProfiledRawJointHybridGuardedCoupledOne A strategy hwin)
    (ownInput : In₁) (deliveredInput : In₂) :
    Out₁ × ProfiledRawJointHybridGuardedCoupledOne A strategy hwin :=
  let input := (ownInput, deliveredInput)
  let common := profiledRawJointHybridGuardedInstallationCommon A strategy hwin
    state.1
  let output := profiledRawJointHybridRootPinnedCommonBothOutput A strategy hwin
    common input
  let nextInstallation :=
    profiledRawJointHybridGuardedNextInstallation A strategy hwin state.1 input
  (output.1,
    initialProfiledRawJointHybridGuardedCoupledOne A strategy hwin
      nextInstallation)

/-- Process-two projection of the same simultaneous round. -/
noncomputable def stepProfiledRawJointHybridGuardedCoupledBothTwo
    (state : ProfiledRawJointHybridGuardedCoupledTwo A strategy hwin)
    (ownInput : In₂) (deliveredInput : In₁) :
    Out₂ × ProfiledRawJointHybridGuardedCoupledTwo A strategy hwin :=
  let input := (deliveredInput, ownInput)
  let common := profiledRawJointHybridGuardedInstallationCommon A strategy hwin
    state.1
  let output := profiledRawJointHybridRootPinnedCommonBothOutput A strategy hwin
    common input
  let nextInstallation :=
    profiledRawJointHybridGuardedNextInstallation A strategy hwin state.1 input
  (output.2,
    initialProfiledRawJointHybridGuardedCoupledTwo A strategy hwin
      nextInstallation)

/-- With the same retained installation, the two local simultaneous
projections form the one literal root-pinned output pair. -/
theorem profiledRawJointHybridGuardedCoupledBoth_outputs
    (one : ProfiledRawJointHybridGuardedCoupledOne A strategy hwin)
    (two : ProfiledRawJointHybridGuardedCoupledTwo A strategy hwin)
    (hinstallation : one.1 = two.1)
    (input : In₁ × In₂) :
    ((stepProfiledRawJointHybridGuardedCoupledBothOne A strategy hwin one
        input.1 input.2).1,
      (stepProfiledRawJointHybridGuardedCoupledBothTwo A strategy hwin two
        input.2 input.1).1) =
      profiledRawJointHybridRootPinnedCommonBothOutput A strategy hwin
        (profiledRawJointHybridGuardedInstallationCommon A strategy hwin
          one.1) input := by
  simp [stepProfiledRawJointHybridGuardedCoupledBothOne,
    stepProfiledRawJointHybridGuardedCoupledBothTwo, hinstallation]

@[simp] theorem profiledRawJointHybridGuardedCoupledBothOne_installation
    (state : ProfiledRawJointHybridGuardedCoupledOne A strategy hwin)
    (input : In₁ × In₂) :
    (stepProfiledRawJointHybridGuardedCoupledBothOne A strategy hwin state
      input.1 input.2).2.1 =
      profiledRawJointHybridGuardedNextInstallation A strategy hwin state.1
        input :=
  rfl

@[simp] theorem profiledRawJointHybridGuardedCoupledBothTwo_installation
    (state : ProfiledRawJointHybridGuardedCoupledTwo A strategy hwin)
    (input : In₁ × In₂) :
    (stepProfiledRawJointHybridGuardedCoupledBothTwo A strategy hwin state
      input.2 input.1).2.1 =
      profiledRawJointHybridGuardedNextInstallation A strategy hwin state.1
        input :=
  rfl

/-! ## First and continuing strict rounds -/

/-- A process-one non-receive resolves the ambiguity as a right block and
advances the retained guarded-right sender. -/
noncomputable def startProfiledRawJointHybridGuardedRightOwner
    (state : ProfiledRawJointHybridGuardedCoupledOne A strategy hwin)
    (input : In₁) :
    Out₁ × ProfiledRawJointHybridGuardedRightInstalledOwner A strategy hwin :=
  let move := profiledRawJointHybridGuardedRightMoveAt A strategy hwin state.1
  let controller := move.memberController A false
  let label := controller.labelOf state.2
  (label.1 input, ⟨state.1, controller.step state.2 input⟩)

/-- Process-two/left-owner mirror. -/
noncomputable def startProfiledRawJointHybridGuardedLeftOwner
    (state : ProfiledRawJointHybridGuardedCoupledTwo A strategy hwin)
    (input : In₂) :
    Out₂ × ProfiledRawJointHybridGuardedLeftInstalledOwner A strategy hwin :=
  let move := profiledRawJointHybridGuardedLeftMoveAt A strategy hwin state.1
  let controller := move.memberController A false
  let label := controller.labelOf state.2
  (label.1 input, ⟨state.1, controller.step state.2 input⟩)

/-- Receiving the delivered guarded-right sender starts its matching right
receiver at the common predecessor row and executes the same strict round. -/
noncomputable def startProfiledRawJointHybridGuardedRightReceiver
    (delivered : ProfiledRawJointHybridGuardedCoupledOne A strategy hwin)
    (ownInput : In₂) (deliveredInput : In₁) :
    Out₂ ×
      ProfiledRawJointHybridGuardedRightInstalledReceiver A strategy hwin :=
  let initial := initialProfiledRawJointHybridGuardedRightReceiver A strategy
    hwin delivered.1 .both
  let next := stepProfiledRawJointHybridGuardedRightReceiverAt A strategy hwin
    delivered.1 delivered.2 initial.2 (ownInput, deliveredInput)
  (next.1, ⟨delivered.1, next.2⟩)

/-- Receiving the guarded-left sender starts the left receiver. -/
noncomputable def startProfiledRawJointHybridGuardedLeftReceiver
    (delivered : ProfiledRawJointHybridGuardedCoupledTwo A strategy hwin)
    (ownInput : In₁) (deliveredInput : In₂) :
    Out₁ ×
      ProfiledRawJointHybridGuardedLeftInstalledReceiver A strategy hwin :=
  let initial := initialProfiledRawJointHybridGuardedLeftReceiver A strategy
    hwin delivered.1 .both
  let next := stepProfiledRawJointHybridGuardedLeftReceiverAt A strategy hwin
    delivered.1 delivered.2 initial.2 (ownInput, deliveredInput)
  (next.1, ⟨delivered.1, next.2⟩)

/-- Blind continuation of an established guarded-right sender. -/
noncomputable def stepProfiledRawJointHybridGuardedRightOwner
    (state : ProfiledRawJointHybridGuardedRightInstalledOwner A strategy hwin)
    (input : In₁) :
    Out₁ × ProfiledRawJointHybridGuardedRightInstalledOwner A strategy hwin :=
  let move := profiledRawJointHybridGuardedRightMoveAt A strategy hwin state.1
  let controller := move.memberController A false
  let label := controller.labelOf state.2
  (label.1 input, ⟨state.1, controller.step state.2 input⟩)

/-- Blind left-sender continuation. -/
noncomputable def stepProfiledRawJointHybridGuardedLeftOwner
    (state : ProfiledRawJointHybridGuardedLeftInstalledOwner A strategy hwin)
    (input : In₂) :
    Out₂ × ProfiledRawJointHybridGuardedLeftInstalledOwner A strategy hwin :=
  let move := profiledRawJointHybridGuardedLeftMoveAt A strategy hwin state.1
  let controller := move.memberController A false
  let label := controller.labelOf state.2
  (label.1 input, ⟨state.1, controller.step state.2 input⟩)

/-- Continue an established guarded-right receiver with the honestly
delivered owner control. -/
noncomputable def stepProfiledRawJointHybridGuardedRightReceiver
    (state : ProfiledRawJointHybridGuardedRightInstalledReceiver A strategy
      hwin)
    (delivered : ProfiledRawJointHybridGuardedRightInstalledOwner A strategy
      hwin)
    (ownInput : In₂) (deliveredInput : In₁) :
    Out₂ × ProfiledRawJointHybridGuardedRightInstalledReceiver A strategy
      hwin := by
  classical
  exact
  if hinstallation : delivered.1 = state.1 then
    let owner : ProfiledRawJointHybridGuardedRightOwnerAt A strategy hwin
        state.1 := hinstallation ▸ delivered.2
    let next := stepProfiledRawJointHybridGuardedRightReceiverAt A strategy
      hwin state.1 owner state.2 (ownInput, deliveredInput)
    (next.1, ⟨state.1, next.2⟩)
  else
    (default, state)

/-- Continue an established guarded-left receiver. -/
noncomputable def stepProfiledRawJointHybridGuardedLeftReceiver
    (state : ProfiledRawJointHybridGuardedLeftInstalledReceiver A strategy
      hwin)
    (delivered : ProfiledRawJointHybridGuardedLeftInstalledOwner A strategy
      hwin)
    (ownInput : In₁) (deliveredInput : In₂) :
    Out₁ × ProfiledRawJointHybridGuardedLeftInstalledReceiver A strategy
      hwin := by
  classical
  exact
  if hinstallation : delivered.1 = state.1 then
    let owner : ProfiledRawJointHybridGuardedLeftOwnerAt A strategy hwin
        state.1 := hinstallation ▸ delivered.2
    let next := stepProfiledRawJointHybridGuardedLeftReceiverAt A strategy
      hwin state.1 owner state.2 (ownInput, deliveredInput)
    (next.1, ⟨state.1, next.2⟩)
  else
    (default, state)

/-- The checked right receiver takes its honest branch when both delivered
states carry the same installation. -/
theorem stepProfiledRawJointHybridGuardedRightReceiver_same
    (installation : Installation A strategy hwin)
    (state : ProfiledRawJointHybridGuardedRightReceiverAt A strategy hwin
      installation)
    (owner : ProfiledRawJointHybridGuardedRightOwnerAt A strategy hwin
      installation)
    (ownInput : In₂) (deliveredInput : In₁) :
    stepProfiledRawJointHybridGuardedRightReceiver A strategy hwin
        ⟨installation, state⟩ ⟨installation, owner⟩ ownInput deliveredInput =
      let next := stepProfiledRawJointHybridGuardedRightReceiverAt A strategy
        hwin installation owner state (ownInput, deliveredInput)
      (next.1, ⟨installation, next.2⟩) := by
  classical
  unfold stepProfiledRawJointHybridGuardedRightReceiver
  rw [dif_pos rfl]

/-- Left honest-branch mirror. -/
theorem stepProfiledRawJointHybridGuardedLeftReceiver_same
    (installation : Installation A strategy hwin)
    (state : ProfiledRawJointHybridGuardedLeftReceiverAt A strategy hwin
      installation)
    (owner : ProfiledRawJointHybridGuardedLeftOwnerAt A strategy hwin
      installation)
    (ownInput : In₁) (deliveredInput : In₂) :
    stepProfiledRawJointHybridGuardedLeftReceiver A strategy hwin
        ⟨installation, state⟩ ⟨installation, owner⟩ ownInput deliveredInput =
      let next := stepProfiledRawJointHybridGuardedLeftReceiverAt A strategy
        hwin installation owner state (ownInput, deliveredInput)
      (next.1, ⟨installation, next.2⟩) := by
  classical
  unfold stepProfiledRawJointHybridGuardedLeftReceiver
  rw [dif_pos rfl]

/-! ## Checked close payloads retained by strict receivers -/

/-- Resolve the most recently emitted guarded-right target to its mega child
and literal left root. -/
noncomputable def
    profiledRawJointHybridGuardedRightReceiverTargetRoot?
    (state : ProfiledRawJointHybridGuardedRightInstalledReceiver A strategy
      hwin) :
    Option (ProfiledRawJointHybridMegaGuardedRightTargetRoot A strategy hwin
      initialBank) :=
  match state.2.2.2 with
  | none => none
  | some target =>
      profiledRawJointHybridMegaGuardedRightTargetRoot? A strategy hwin
        initialBank state.1 target

/-- Left-receiver mirror. -/
noncomputable def
    profiledRawJointHybridGuardedLeftReceiverTargetRoot?
    (state : ProfiledRawJointHybridGuardedLeftInstalledReceiver A strategy
      hwin) :
    Option (ProfiledRawJointHybridMegaGuardedLeftTargetRoot A strategy hwin
      initialBank) :=
  match state.2.2.2 with
  | none => none
  | some target =>
      profiledRawJointHybridMegaGuardedLeftTargetRoot? A strategy hwin
        initialBank state.1 target

@[simp] theorem profiledRawJointHybridGuardedRightReceiverTargetRoot?_some
    (state : ProfiledRawJointHybridGuardedRightInstalledReceiver A strategy
      hwin)
    (target : ProfiledRawJointUnitTarget A)
    (htarget : state.2.2.2 = some target) :
    profiledRawJointHybridGuardedRightReceiverTargetRoot? A strategy hwin
        initialBank state =
      profiledRawJointHybridMegaGuardedRightTargetRoot? A strategy hwin
        initialBank state.1 target := by
  simp [profiledRawJointHybridGuardedRightReceiverTargetRoot?, htarget]

@[simp] theorem profiledRawJointHybridGuardedLeftReceiverTargetRoot?_some
    (state : ProfiledRawJointHybridGuardedLeftInstalledReceiver A strategy
      hwin)
    (target : ProfiledRawJointUnitTarget A)
    (htarget : state.2.2.2 = some target) :
    profiledRawJointHybridGuardedLeftReceiverTargetRoot? A strategy hwin
        initialBank state =
      profiledRawJointHybridMegaGuardedLeftTargetRoot? A strategy hwin
        initialBank state.1 target := by
  simp [profiledRawJointHybridGuardedLeftReceiverTargetRoot?, htarget]

/-! ## Certified operational prefix states -/

/-- Transport the represented-pair right prefix state once to the exact move
index stored by the installation. -/
noncomputable def profiledRawJointHybridGuardedRightFiniteStateAfter
    (installation : Installation A strategy hwin)
    (past : List (In₂ × In₁)) :
    ((profiledRawJointHybridGuardedRightMoveAt A strategy hwin installation
      ).memberController A false).Control ×
      (profiledRawJointGuardedRightPhysicalSiblingMonitor A
        (profiledRawJointHybridGuardedRightMoveAt A strategy hwin
          installation).1 false).State := by
  cases installation with
  | inl initial =>
      exact profiledRawJointGuardedCommonRightFiniteStateAfter A strategy hwin
        (profiledRawJointHybridGuardedCommonPairAt A strategy hwin
          (.inl initial)) past
  | inr recurrent =>
      exact profiledRawJointGuardedCommonRightFiniteStateAfter A strategy hwin
        (profiledRawJointHybridGuardedCommonPairAt A strategy hwin
          (.inr recurrent)) past

/-- Left transport. -/
noncomputable def profiledRawJointHybridGuardedLeftFiniteStateAfter
    (installation : Installation A strategy hwin)
    (past : List (In₁ × In₂)) :
    ((profiledRawJointHybridGuardedLeftMoveAt A strategy hwin installation
      ).memberController A false).Control ×
      (profiledRawJointGuardedLeftPhysicalSiblingMonitor A
        (profiledRawJointHybridGuardedLeftMoveAt A strategy hwin
          installation).1 false).State := by
  cases installation with
  | inl initial =>
      exact profiledRawJointGuardedCommonLeftFiniteStateAfter A strategy hwin
        (profiledRawJointHybridGuardedCommonPairAt A strategy hwin
          (.inl initial)) past
  | inr recurrent =>
      exact profiledRawJointGuardedCommonLeftFiniteStateAfter A strategy hwin
        (profiledRawJointHybridGuardedCommonPairAt A strategy hwin
          (.inr recurrent)) past

/-- Installed guarded-right owner at the exact finite prefix used by the
generic reachability theorem. -/
noncomputable def profiledRawJointHybridGuardedRightPrefixOwner
    (installation : Installation A strategy hwin)
    (past : List (In₂ × In₁)) :
    ProfiledRawJointHybridGuardedRightInstalledOwner A strategy hwin :=
  let state := profiledRawJointHybridGuardedRightFiniteStateAfter A strategy
    hwin installation past
  ⟨installation, state.1⟩

/-- Matching receiver immediately before the next right-prefix round. -/
noncomputable def profiledRawJointHybridGuardedRightPrefixReceiverBefore
    (installation : Installation A strategy hwin)
    (past : List (In₂ × In₁)) :
    ProfiledRawJointHybridGuardedRightInstalledReceiver A strategy hwin :=
  let state := profiledRawJointHybridGuardedRightFiniteStateAfter A strategy
    hwin installation past
  ⟨installation, .both, state.2, none⟩

/-- Execute the next certified right-prefix receive. -/
noncomputable def profiledRawJointHybridGuardedRightPrefixReceiverAfter
    (installation : Installation A strategy hwin)
    (past : List (In₂ × In₁)) (input : In₂ × In₁) :
    ProfiledRawJointHybridGuardedRightInstalledReceiver A strategy hwin :=
  (stepProfiledRawJointHybridGuardedRightReceiver A strategy hwin
    (profiledRawJointHybridGuardedRightPrefixReceiverBefore A strategy hwin
      installation past)
    (profiledRawJointHybridGuardedRightPrefixOwner A strategy hwin
      installation past) input.1 input.2).2

/-- The operational receiver stores exactly the target certified by the
generic guarded-prefix theorem. -/
theorem profiledRawJointHybridGuardedRightPrefixReceiverAfter_target
    (installation : Installation A strategy hwin)
    (past : List (In₂ × In₁)) (input : In₂ × In₁) :
    let pair := profiledRawJointHybridGuardedCommonPairAt A strategy hwin
      installation
    (profiledRawJointHybridGuardedRightPrefixReceiverAfter A strategy hwin
      installation past input).2.2.2 =
      some ((profiledRawJointGuardedCommonRightPrefixOutput A strategy hwin
        pair past input).target .both) := by
  classical
  unfold profiledRawJointHybridGuardedRightPrefixReceiverAfter
  unfold profiledRawJointHybridGuardedRightPrefixReceiverBefore
  unfold profiledRawJointHybridGuardedRightPrefixOwner
  rw [stepProfiledRawJointHybridGuardedRightReceiver_same]
  cases installation <;> rfl

@[simp] theorem
    profiledRawJointHybridGuardedRightPrefixReceiverAfter_installation
    (installation : Installation A strategy hwin)
    (past : List (In₂ × In₁)) (input : In₂ × In₁) :
    (profiledRawJointHybridGuardedRightPrefixReceiverAfter A strategy hwin
      installation past input).1 = installation := by
  classical
  unfold profiledRawJointHybridGuardedRightPrefixReceiverAfter
  unfold profiledRawJointHybridGuardedRightPrefixReceiverBefore
  unfold profiledRawJointHybridGuardedRightPrefixOwner
  rw [stepProfiledRawJointHybridGuardedRightReceiver_same]

/-- The exact executable root lookup succeeds on every certified right
prefix. -/
theorem
    exists_profiledRawJointHybridGuardedRightPrefixReceiverAfter_targetRoot
    (installation : Installation A strategy hwin)
    (past : List (In₂ × In₁)) (input : In₂ × In₁) :
    ∃ root,
      profiledRawJointHybridGuardedRightReceiverTargetRoot? A strategy hwin
          initialBank
          (profiledRawJointHybridGuardedRightPrefixReceiverAfter A strategy
            hwin installation past input) = some root := by
  classical
  let target :=
    (profiledRawJointGuardedCommonRightPrefixOutput A strategy hwin
      (profiledRawJointHybridGuardedCommonPairAt A strategy hwin installation)
      past input).target .both
  have htarget :=
    profiledRawJointHybridGuardedRightPrefixReceiverAfter_target A strategy
      hwin installation past input
  have hroot :=
    exists_profiledRawJointHybridMegaGuardedRightTargetRoot_at_prefix A
      strategy hwin initialBank installation past input .both
  rw [profiledRawJointHybridGuardedRightReceiverTargetRoot?_some A strategy
    hwin initialBank _ target htarget]
  rw [profiledRawJointHybridGuardedRightPrefixReceiverAfter_installation]
  exact hroot

/-- Installed guarded-left owner at an exact finite prefix. -/
noncomputable def profiledRawJointHybridGuardedLeftPrefixOwner
    (installation : Installation A strategy hwin)
    (past : List (In₁ × In₂)) :
    ProfiledRawJointHybridGuardedLeftInstalledOwner A strategy hwin :=
  let state := profiledRawJointHybridGuardedLeftFiniteStateAfter A strategy
    hwin installation past
  ⟨installation, state.1⟩

/-- Matching left receiver before the next certified prefix round. -/
noncomputable def profiledRawJointHybridGuardedLeftPrefixReceiverBefore
    (installation : Installation A strategy hwin)
    (past : List (In₁ × In₂)) :
    ProfiledRawJointHybridGuardedLeftInstalledReceiver A strategy hwin :=
  let state := profiledRawJointHybridGuardedLeftFiniteStateAfter A strategy
    hwin installation past
  ⟨installation, .both, state.2, none⟩

/-- Execute the next certified left-prefix receive. -/
noncomputable def profiledRawJointHybridGuardedLeftPrefixReceiverAfter
    (installation : Installation A strategy hwin)
    (past : List (In₁ × In₂)) (input : In₁ × In₂) :
    ProfiledRawJointHybridGuardedLeftInstalledReceiver A strategy hwin :=
  (stepProfiledRawJointHybridGuardedLeftReceiver A strategy hwin
    (profiledRawJointHybridGuardedLeftPrefixReceiverBefore A strategy hwin
      installation past)
    (profiledRawJointHybridGuardedLeftPrefixOwner A strategy hwin installation
      past) input.1 input.2).2

theorem profiledRawJointHybridGuardedLeftPrefixReceiverAfter_target
    (installation : Installation A strategy hwin)
    (past : List (In₁ × In₂)) (input : In₁ × In₂) :
    let pair := profiledRawJointHybridGuardedCommonPairAt A strategy hwin
      installation
    (profiledRawJointHybridGuardedLeftPrefixReceiverAfter A strategy hwin
      installation past input).2.2.2 =
      some ((profiledRawJointGuardedCommonLeftPrefixOutput A strategy hwin pair
        past input).target .both) := by
  classical
  unfold profiledRawJointHybridGuardedLeftPrefixReceiverAfter
  unfold profiledRawJointHybridGuardedLeftPrefixReceiverBefore
  unfold profiledRawJointHybridGuardedLeftPrefixOwner
  rw [stepProfiledRawJointHybridGuardedLeftReceiver_same]
  cases installation <;> rfl

@[simp] theorem
    profiledRawJointHybridGuardedLeftPrefixReceiverAfter_installation
    (installation : Installation A strategy hwin)
    (past : List (In₁ × In₂)) (input : In₁ × In₂) :
    (profiledRawJointHybridGuardedLeftPrefixReceiverAfter A strategy hwin
      installation past input).1 = installation := by
  classical
  unfold profiledRawJointHybridGuardedLeftPrefixReceiverAfter
  unfold profiledRawJointHybridGuardedLeftPrefixReceiverBefore
  unfold profiledRawJointHybridGuardedLeftPrefixOwner
  rw [stepProfiledRawJointHybridGuardedLeftReceiver_same]

/-- Left operational root lookup succeeds on every certified prefix. -/
theorem exists_profiledRawJointHybridGuardedLeftPrefixReceiverAfter_targetRoot
    (installation : Installation A strategy hwin)
    (past : List (In₁ × In₂)) (input : In₁ × In₂) :
    ∃ root,
      profiledRawJointHybridGuardedLeftReceiverTargetRoot? A strategy hwin
          initialBank
          (profiledRawJointHybridGuardedLeftPrefixReceiverAfter A strategy
            hwin installation past input) = some root := by
  classical
  let target :=
    (profiledRawJointGuardedCommonLeftPrefixOutput A strategy hwin
      (profiledRawJointHybridGuardedCommonPairAt A strategy hwin installation)
      past input).target .both
  have htarget :=
    profiledRawJointHybridGuardedLeftPrefixReceiverAfter_target A strategy hwin
      installation past input
  have hroot :=
    exists_profiledRawJointHybridMegaGuardedLeftTargetRoot_at_prefix A strategy
      hwin initialBank installation past input .both
  rw [profiledRawJointHybridGuardedLeftReceiverTargetRoot?_some A strategy hwin
    initialBank _ target htarget]
  rw [profiledRawJointHybridGuardedLeftPrefixReceiverAfter_installation]
  exact hroot

end

end DetParityAutomaton

end DistributedSynthesis
