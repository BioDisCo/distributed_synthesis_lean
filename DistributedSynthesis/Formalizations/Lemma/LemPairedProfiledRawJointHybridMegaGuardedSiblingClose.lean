/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridGuardedSiblingCoupledFront

/-!
# Closing the guarded sibling front into the mega family

The coupled guarded front retains a checked target at its receiver.  This file
turns the corresponding literal root into the ordinary recurrent controls of
the seven-way mega family.  The four partial transition functions are exactly
the four local rows needed at a hierarchy reversal or simultaneous close.

Failure remains explicit for malformed finite states.  On every certified
finite prefix, the reachability theorem from the coupled front proves that the
lookup succeeds, so the operational run never takes that fallback branch.
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

private abbrev Child :=
  ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank

abbrev ProfiledRawJointHybridMegaGuardedStartedRightOwner :=
  Σ child : Child A strategy hwin initialBank,
    ProfiledRawJointHybridMegaRightOwner A strategy hwin initialBank child

abbrev ProfiledRawJointHybridMegaGuardedStartedLeftReceiver :=
  Σ child : Child A strategy hwin initialBank,
    ProfiledRawJointHybridMegaLeftReceiver A strategy hwin initialBank child

abbrev ProfiledRawJointHybridMegaGuardedStartedRightReceiver :=
  Σ child : Child A strategy hwin initialBank,
    ProfiledRawJointHybridMegaRightReceiver A strategy hwin initialBank child

abbrev ProfiledRawJointHybridMegaGuardedStartedLeftOwner :=
  Σ child : Child A strategy hwin initialBank,
    ProfiledRawJointHybridMegaLeftOwner A strategy hwin initialBank child

/-! ## Right-table close -/

/-- A process-one receive closes a delivered guarded-right receiver into the
ordinary left receiver at its literal root. -/
noncomputable def profiledRawJointHybridMegaGuardedRightCloseReceiverOne?
    (state : ProfiledRawJointHybridGuardedRightInstalledReceiver A strategy
      hwin)
    (ownInput : In₁) (deliveredInput : In₂) :
    Option (Out₁ ×
      ProfiledRawJointHybridMegaGuardedStartedLeftReceiver A strategy hwin
        initialBank) :=
  match profiledRawJointHybridGuardedRightReceiverTargetRoot? A strategy hwin
      initialBank state with
  | none => none
  | some root =>
      let child := root.1
      let source := profiledRawJointHybridMegaChildSource A strategy hwin
        initialBank child
      let policy := profiledRawJointHybridMegaChildPolicy A strategy hwin
        initialBank child
      let bank := profiledRawJointHybridMegaChildControllerBank A strategy hwin
        initialBank child
      let restart := profiledRawJointUnitRestartLeft A strategy source policy
        bank root.2 .first
      let next := continueProfiledRawJointUnitLeftPolicyReceiver A strategy
        source policy bank restart.2 restart.1 (ownInput, deliveredInput)
      some (next.1, ⟨child, next.2⟩)

/-- Simultaneous-history companion of the preceding close.  This branch is
used after a first simultaneous round has refreshed the guarded receiver's
target.  The refreshed target's `.both` coordinate represents that first
round and is therefore the predecessor of the repeated-simultaneous close. -/
noncomputable def
    profiledRawJointHybridMegaGuardedRightCloseReceiverOneBoth?
    (state : ProfiledRawJointHybridGuardedRightInstalledReceiver A strategy
      hwin)
    (ownInput : In₁) (deliveredInput : In₂) :
    Option (Out₁ ×
      ProfiledRawJointHybridMegaGuardedStartedLeftReceiver A strategy hwin
        initialBank) :=
  match profiledRawJointHybridGuardedRightReceiverTargetRoot? A strategy hwin
      initialBank state with
  | none => none
  | some root =>
      let child := root.1
      let source := profiledRawJointHybridMegaChildSource A strategy hwin
        initialBank child
      let policy := profiledRawJointHybridMegaChildPolicy A strategy hwin
        initialBank child
      let bank := profiledRawJointHybridMegaChildControllerBank A strategy hwin
        initialBank child
      let restart := profiledRawJointUnitRestartLeft A strategy source policy
        bank root.2 .both
      let next := continueProfiledRawJointUnitLeftPolicyReceiver A strategy
        source policy bank restart.2 restart.1 (ownInput, deliveredInput)
      some (next.1, ⟨child, next.2⟩)

/-- Process-two companion of the simultaneous right-target close.  Both
endpoints select the guarded-right target.  Process two starts the ordinary
right receiver from the same restarted left receiver used by process one, so
the resulting receiver cross is indexed by one literal mega child. -/
noncomputable def
    profiledRawJointHybridMegaGuardedRightCloseReceiverTwoBoth?
    (state : ProfiledRawJointHybridGuardedRightInstalledReceiver A strategy
      hwin)
    (ownInput : In₂) (deliveredInput : In₁) :
    Option (Out₂ ×
      ProfiledRawJointHybridMegaGuardedStartedRightReceiver A strategy hwin
        initialBank) :=
  match profiledRawJointHybridGuardedRightReceiverTargetRoot? A strategy hwin
      initialBank state with
  | none => none
  | some root =>
      let child := root.1
      let source := profiledRawJointHybridMegaChildSource A strategy hwin
        initialBank child
      let policy := profiledRawJointHybridMegaChildPolicy A strategy hwin
        initialBank child
      let bank := profiledRawJointHybridMegaChildControllerBank A strategy hwin
        initialBank child
      let restart := profiledRawJointUnitRestartLeft A strategy source policy
        bank root.2 .both
      let next := profiledRawJointUnitPolicyStartRightReceiver A strategy
        source policy bank restart.2 (ownInput, deliveredInput)
      some (next.1, ⟨child, next.2⟩)

/-- A process-two non-receive starts the matching ordinary left owner. -/
noncomputable def profiledRawJointHybridMegaGuardedRightCloseOwnerTwo?
    (state : ProfiledRawJointHybridGuardedRightInstalledReceiver A strategy
      hwin)
    (input : In₂) :
    Option (Out₂ ×
      ProfiledRawJointHybridMegaGuardedStartedLeftOwner A strategy hwin
        initialBank) :=
  match profiledRawJointHybridGuardedRightReceiverTargetRoot? A strategy hwin
      initialBank state with
  | none => none
  | some root =>
      let child := root.1
      let source := profiledRawJointHybridMegaChildSource A strategy hwin
        initialBank child
      let policy := profiledRawJointHybridMegaChildPolicy A strategy hwin
        initialBank child
      let bank := profiledRawJointHybridMegaChildControllerBank A strategy hwin
        initialBank child
      let owner := initialProfiledRawJointUnitLeftPolicyOwner A strategy source
        policy bank root.2
      let next := stepProfiledRawJointUnitLeftPolicyOwner A strategy source
        policy bank owner input
      some (next.1, ⟨child, next.2⟩)

@[simp] theorem profiledRawJointHybridMegaGuardedRightCloseReceiverOne?_some
    (state : ProfiledRawJointHybridGuardedRightInstalledReceiver A strategy
      hwin)
    (root : ProfiledRawJointHybridMegaGuardedRightTargetRoot A strategy hwin
      initialBank)
    (hroot :
      profiledRawJointHybridGuardedRightReceiverTargetRoot? A strategy hwin
        initialBank state = some root)
    (ownInput : In₁) (deliveredInput : In₂) :
    profiledRawJointHybridMegaGuardedRightCloseReceiverOne? A strategy hwin
        initialBank state ownInput deliveredInput =
      let child := root.1
      let source := profiledRawJointHybridMegaChildSource A strategy hwin
        initialBank child
      let policy := profiledRawJointHybridMegaChildPolicy A strategy hwin
        initialBank child
      let bank := profiledRawJointHybridMegaChildControllerBank A strategy hwin
        initialBank child
      let restart := profiledRawJointUnitRestartLeft A strategy source policy
        bank root.2 .first
      let next := continueProfiledRawJointUnitLeftPolicyReceiver A strategy
        source policy bank restart.2 restart.1 (ownInput, deliveredInput)
      some (next.1, ⟨child, next.2⟩) := by
  simp [profiledRawJointHybridMegaGuardedRightCloseReceiverOne?, hroot]

@[simp] theorem
    profiledRawJointHybridMegaGuardedRightCloseReceiverOneBoth?_some
    (state : ProfiledRawJointHybridGuardedRightInstalledReceiver A strategy
      hwin)
    (root : ProfiledRawJointHybridMegaGuardedRightTargetRoot A strategy hwin
      initialBank)
    (hroot :
      profiledRawJointHybridGuardedRightReceiverTargetRoot? A strategy hwin
        initialBank state = some root)
    (ownInput : In₁) (deliveredInput : In₂) :
    profiledRawJointHybridMegaGuardedRightCloseReceiverOneBoth? A strategy hwin
        initialBank state ownInput deliveredInput =
      let child := root.1
      let source := profiledRawJointHybridMegaChildSource A strategy hwin
        initialBank child
      let policy := profiledRawJointHybridMegaChildPolicy A strategy hwin
        initialBank child
      let bank := profiledRawJointHybridMegaChildControllerBank A strategy hwin
        initialBank child
      let restart := profiledRawJointUnitRestartLeft A strategy source policy
        bank root.2 .both
      let next := continueProfiledRawJointUnitLeftPolicyReceiver A strategy
        source policy bank restart.2 restart.1 (ownInput, deliveredInput)
      some (next.1, ⟨child, next.2⟩) := by
  simp [profiledRawJointHybridMegaGuardedRightCloseReceiverOneBoth?, hroot]

@[simp] theorem
    profiledRawJointHybridMegaGuardedRightCloseReceiverTwoBoth?_some
    (state : ProfiledRawJointHybridGuardedRightInstalledReceiver A strategy
      hwin)
    (root : ProfiledRawJointHybridMegaGuardedRightTargetRoot A strategy hwin
      initialBank)
    (hroot :
      profiledRawJointHybridGuardedRightReceiverTargetRoot? A strategy hwin
        initialBank state = some root)
    (ownInput : In₂) (deliveredInput : In₁) :
    profiledRawJointHybridMegaGuardedRightCloseReceiverTwoBoth? A strategy hwin
        initialBank state ownInput deliveredInput =
      let child := root.1
      let source := profiledRawJointHybridMegaChildSource A strategy hwin
        initialBank child
      let policy := profiledRawJointHybridMegaChildPolicy A strategy hwin
        initialBank child
      let bank := profiledRawJointHybridMegaChildControllerBank A strategy hwin
        initialBank child
      let restart := profiledRawJointUnitRestartLeft A strategy source policy
        bank root.2 .both
      let next := profiledRawJointUnitPolicyStartRightReceiver A strategy
        source policy bank restart.2 (ownInput, deliveredInput)
      some (next.1, ⟨child, next.2⟩) := by
  simp [profiledRawJointHybridMegaGuardedRightCloseReceiverTwoBoth?, hroot]

@[simp] theorem profiledRawJointHybridMegaGuardedRightCloseOwnerTwo?_some
    (state : ProfiledRawJointHybridGuardedRightInstalledReceiver A strategy
      hwin)
    (root : ProfiledRawJointHybridMegaGuardedRightTargetRoot A strategy hwin
      initialBank)
    (hroot :
      profiledRawJointHybridGuardedRightReceiverTargetRoot? A strategy hwin
        initialBank state = some root)
    (input : In₂) :
    profiledRawJointHybridMegaGuardedRightCloseOwnerTwo? A strategy hwin
        initialBank state input =
      let child := root.1
      let source := profiledRawJointHybridMegaChildSource A strategy hwin
        initialBank child
      let policy := profiledRawJointHybridMegaChildPolicy A strategy hwin
        initialBank child
      let bank := profiledRawJointHybridMegaChildControllerBank A strategy hwin
        initialBank child
      let owner := initialProfiledRawJointUnitLeftPolicyOwner A strategy source
        policy bank root.2
      let next := stepProfiledRawJointUnitLeftPolicyOwner A strategy source
        policy bank owner input
      some (next.1, ⟨child, next.2⟩) := by
  simp [profiledRawJointHybridMegaGuardedRightCloseOwnerTwo?, hroot]

/-! ## Left-table close -/

/-- A process-one non-receive starts the ordinary right owner selected by a
guarded-left target. -/
noncomputable def profiledRawJointHybridMegaGuardedLeftCloseOwnerOne?
    (state : ProfiledRawJointHybridGuardedLeftInstalledReceiver A strategy
      hwin)
    (input : In₁) :
    Option (Out₁ ×
      ProfiledRawJointHybridMegaGuardedStartedRightOwner A strategy hwin
        initialBank) :=
  match profiledRawJointHybridGuardedLeftReceiverTargetRoot? A strategy hwin
      initialBank state with
  | none => none
  | some root =>
      let child := root.1
      let source := profiledRawJointHybridMegaChildSource A strategy hwin
        initialBank child
      let policy := profiledRawJointHybridMegaChildPolicy A strategy hwin
        initialBank child
      let bank := profiledRawJointHybridMegaChildControllerBank A strategy hwin
        initialBank child
      let owner := initialProfiledRawJointUnitRightPolicyOwner A strategy source
        policy bank root.2
      let next := stepProfiledRawJointUnitRightPolicyOwner A strategy source
        policy bank owner input
      some (next.1, ⟨child, next.2⟩)

/-- Process-two receive starts the matching ordinary right receiver. -/
noncomputable def profiledRawJointHybridMegaGuardedLeftCloseReceiverTwo?
    (state : ProfiledRawJointHybridGuardedLeftInstalledReceiver A strategy
      hwin)
    (ownInput : In₂) (deliveredInput : In₁) :
    Option (Out₂ ×
      ProfiledRawJointHybridMegaGuardedStartedRightReceiver A strategy hwin
        initialBank) :=
  match profiledRawJointHybridGuardedLeftReceiverTargetRoot? A strategy hwin
      initialBank state with
  | none => none
  | some root =>
      let child := root.1
      let source := profiledRawJointHybridMegaChildSource A strategy hwin
        initialBank child
      let policy := profiledRawJointHybridMegaChildPolicy A strategy hwin
        initialBank child
      let bank := profiledRawJointHybridMegaChildControllerBank A strategy hwin
        initialBank child
      let restart := profiledRawJointUnitRestartRight A strategy source policy
        bank root.2 .first
      let next := continueProfiledRawJointUnitRightPolicyReceiver A strategy
        source policy bank restart.2 restart.1 (ownInput, deliveredInput)
      some (next.1, ⟨child, next.2⟩)

/-- Simultaneous-history mirror, rooted at the refreshed target's `.both`
coordinate. -/
noncomputable def
    profiledRawJointHybridMegaGuardedLeftCloseReceiverTwoBoth?
    (state : ProfiledRawJointHybridGuardedLeftInstalledReceiver A strategy
      hwin)
    (ownInput : In₂) (deliveredInput : In₁) :
    Option (Out₂ ×
      ProfiledRawJointHybridMegaGuardedStartedRightReceiver A strategy hwin
        initialBank) :=
  match profiledRawJointHybridGuardedLeftReceiverTargetRoot? A strategy hwin
      initialBank state with
  | none => none
  | some root =>
      let child := root.1
      let source := profiledRawJointHybridMegaChildSource A strategy hwin
        initialBank child
      let policy := profiledRawJointHybridMegaChildPolicy A strategy hwin
        initialBank child
      let bank := profiledRawJointHybridMegaChildControllerBank A strategy hwin
        initialBank child
      let restart := profiledRawJointUnitRestartRight A strategy source policy
        bank root.2 .both
      let next := continueProfiledRawJointUnitRightPolicyReceiver A strategy
        source policy bank restart.2 restart.1 (ownInput, deliveredInput)
      some (next.1, ⟨child, next.2⟩)

@[simp] theorem profiledRawJointHybridMegaGuardedLeftCloseOwnerOne?_some
    (state : ProfiledRawJointHybridGuardedLeftInstalledReceiver A strategy
      hwin)
    (root : ProfiledRawJointHybridMegaGuardedLeftTargetRoot A strategy hwin
      initialBank)
    (hroot :
      profiledRawJointHybridGuardedLeftReceiverTargetRoot? A strategy hwin
        initialBank state = some root)
    (input : In₁) :
    profiledRawJointHybridMegaGuardedLeftCloseOwnerOne? A strategy hwin
        initialBank state input =
      let child := root.1
      let source := profiledRawJointHybridMegaChildSource A strategy hwin
        initialBank child
      let policy := profiledRawJointHybridMegaChildPolicy A strategy hwin
        initialBank child
      let bank := profiledRawJointHybridMegaChildControllerBank A strategy hwin
        initialBank child
      let owner := initialProfiledRawJointUnitRightPolicyOwner A strategy source
        policy bank root.2
      let next := stepProfiledRawJointUnitRightPolicyOwner A strategy source
        policy bank owner input
      some (next.1, ⟨child, next.2⟩) := by
  simp [profiledRawJointHybridMegaGuardedLeftCloseOwnerOne?, hroot]

@[simp] theorem profiledRawJointHybridMegaGuardedLeftCloseReceiverTwo?_some
    (state : ProfiledRawJointHybridGuardedLeftInstalledReceiver A strategy
      hwin)
    (root : ProfiledRawJointHybridMegaGuardedLeftTargetRoot A strategy hwin
      initialBank)
    (hroot :
      profiledRawJointHybridGuardedLeftReceiverTargetRoot? A strategy hwin
        initialBank state = some root)
    (ownInput : In₂) (deliveredInput : In₁) :
    profiledRawJointHybridMegaGuardedLeftCloseReceiverTwo? A strategy hwin
        initialBank state ownInput deliveredInput =
      let child := root.1
      let source := profiledRawJointHybridMegaChildSource A strategy hwin
        initialBank child
      let policy := profiledRawJointHybridMegaChildPolicy A strategy hwin
        initialBank child
      let bank := profiledRawJointHybridMegaChildControllerBank A strategy hwin
        initialBank child
      let restart := profiledRawJointUnitRestartRight A strategy source policy
        bank root.2 .first
      let next := continueProfiledRawJointUnitRightPolicyReceiver A strategy
        source policy bank restart.2 restart.1 (ownInput, deliveredInput)
      some (next.1, ⟨child, next.2⟩) := by
  simp [profiledRawJointHybridMegaGuardedLeftCloseReceiverTwo?, hroot]

@[simp] theorem
    profiledRawJointHybridMegaGuardedLeftCloseReceiverTwoBoth?_some
    (state : ProfiledRawJointHybridGuardedLeftInstalledReceiver A strategy
      hwin)
    (root : ProfiledRawJointHybridMegaGuardedLeftTargetRoot A strategy hwin
      initialBank)
    (hroot :
      profiledRawJointHybridGuardedLeftReceiverTargetRoot? A strategy hwin
        initialBank state = some root)
    (ownInput : In₂) (deliveredInput : In₁) :
    profiledRawJointHybridMegaGuardedLeftCloseReceiverTwoBoth? A strategy hwin
        initialBank state ownInput deliveredInput =
      let child := root.1
      let source := profiledRawJointHybridMegaChildSource A strategy hwin
        initialBank child
      let policy := profiledRawJointHybridMegaChildPolicy A strategy hwin
        initialBank child
      let bank := profiledRawJointHybridMegaChildControllerBank A strategy hwin
        initialBank child
      let restart := profiledRawJointUnitRestartRight A strategy source policy
        bank root.2 .both
      let next := continueProfiledRawJointUnitRightPolicyReceiver A strategy
        source policy bank restart.2 restart.1 (ownInput, deliveredInput)
      some (next.1, ⟨child, next.2⟩) := by
  simp [profiledRawJointHybridMegaGuardedLeftCloseReceiverTwoBoth?, hroot]

/-! ## Certified prefix success -/

theorem exists_profiledRawJointHybridMegaGuardedRightPrefixClose
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (nextInputOne : In₁) (nextInputTwo : In₂) :
    (∃ next,
      profiledRawJointHybridMegaGuardedRightCloseReceiverOne? A strategy hwin
        initialBank
          (profiledRawJointHybridGuardedRightPrefixReceiverAfter A strategy
            hwin installation past input) nextInputOne nextInputTwo =
        some next) ∧
    (∃ next,
      profiledRawJointHybridMegaGuardedRightCloseOwnerTwo? A strategy hwin
        initialBank
          (profiledRawJointHybridGuardedRightPrefixReceiverAfter A strategy
            hwin installation past input) nextInputTwo = some next) := by
  rcases
      exists_profiledRawJointHybridGuardedRightPrefixReceiverAfter_targetRoot
        A strategy hwin initialBank installation past input with
    ⟨root, hroot⟩
  constructor
  · rw [profiledRawJointHybridMegaGuardedRightCloseReceiverOne?_some A
      strategy hwin initialBank _ root hroot]
    exact ⟨_, rfl⟩
  · rw [profiledRawJointHybridMegaGuardedRightCloseOwnerTwo?_some A strategy
      hwin initialBank _ root hroot]
    exact ⟨_, rfl⟩

/-- The two local right-prefix close rows install one and the same mega child.
This is stronger than separate lookup success and is the exact synchronization
fact consumed by the indexed recurrent carrier. -/
theorem
    exists_profiledRawJointHybridMegaGuardedRightPrefixClose_sameChild
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (nextInputOne : In₁) (nextInputTwo : In₂) :
    ∃ child outputOne receiver outputTwo owner,
      profiledRawJointHybridMegaGuardedRightCloseReceiverOne? A strategy hwin
          initialBank
            (profiledRawJointHybridGuardedRightPrefixReceiverAfter A strategy
              hwin installation past input) nextInputOne nextInputTwo =
        some (outputOne, ⟨child, receiver⟩) ∧
      profiledRawJointHybridMegaGuardedRightCloseOwnerTwo? A strategy hwin
          initialBank
            (profiledRawJointHybridGuardedRightPrefixReceiverAfter A strategy
              hwin installation past input) nextInputTwo =
        some (outputTwo, ⟨child, owner⟩) := by
  rcases
      exists_profiledRawJointHybridGuardedRightPrefixReceiverAfter_targetRoot
        A strategy hwin initialBank installation past input with
    ⟨root, hroot⟩
  rw [profiledRawJointHybridMegaGuardedRightCloseReceiverOne?_some A strategy
      hwin initialBank _ root hroot,
    profiledRawJointHybridMegaGuardedRightCloseOwnerTwo?_some A strategy hwin
      initialBank _ root hroot]
  exact ⟨root.1, _, _, _, _, rfl, rfl⟩

/-- A certified strict-right prefix also makes the deterministic simultaneous
anchor close succeed at both endpoints, with one common child key. -/
theorem
    exists_profiledRawJointHybridMegaGuardedRightPrefixCloseBoth_sameChild
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (nextInputOne : In₁) (nextInputTwo : In₂) :
    ∃ child outputOne leftReceiver outputTwo rightReceiver,
      profiledRawJointHybridMegaGuardedRightCloseReceiverOneBoth? A strategy
          hwin initialBank
            (profiledRawJointHybridGuardedRightPrefixReceiverAfter A strategy
              hwin installation past input) nextInputOne nextInputTwo =
        some (outputOne, ⟨child, leftReceiver⟩) ∧
      profiledRawJointHybridMegaGuardedRightCloseReceiverTwoBoth? A strategy
          hwin initialBank
            (profiledRawJointHybridGuardedRightPrefixReceiverAfter A strategy
              hwin installation past input) nextInputTwo nextInputOne =
        some (outputTwo, ⟨child, rightReceiver⟩) := by
  rcases
      exists_profiledRawJointHybridGuardedRightPrefixReceiverAfter_targetRoot
        A strategy hwin initialBank installation past input with
    ⟨root, hroot⟩
  rw [profiledRawJointHybridMegaGuardedRightCloseReceiverOneBoth?_some A
      strategy hwin initialBank _ root hroot,
    profiledRawJointHybridMegaGuardedRightCloseReceiverTwoBoth?_some A
      strategy hwin initialBank _ root hroot]
  exact ⟨root.1, _, _, _, _, rfl, rfl⟩

theorem exists_profiledRawJointHybridMegaGuardedLeftPrefixClose
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (past : List (In₁ × In₂)) (input : In₁ × In₂)
    (nextInputOne : In₁) (nextInputTwo : In₂) :
    (∃ next,
      profiledRawJointHybridMegaGuardedLeftCloseOwnerOne? A strategy hwin
        initialBank
          (profiledRawJointHybridGuardedLeftPrefixReceiverAfter A strategy hwin
            installation past input) nextInputOne = some next) ∧
    (∃ next,
      profiledRawJointHybridMegaGuardedLeftCloseReceiverTwo? A strategy hwin
        initialBank
          (profiledRawJointHybridGuardedLeftPrefixReceiverAfter A strategy hwin
            installation past input) nextInputTwo nextInputOne = some next) := by
  rcases
      exists_profiledRawJointHybridGuardedLeftPrefixReceiverAfter_targetRoot A
        strategy hwin initialBank installation past input with
    ⟨root, hroot⟩
  constructor
  · rw [profiledRawJointHybridMegaGuardedLeftCloseOwnerOne?_some A strategy
      hwin initialBank _ root hroot]
    exact ⟨_, rfl⟩
  · rw [profiledRawJointHybridMegaGuardedLeftCloseReceiverTwo?_some A strategy
      hwin initialBank _ root hroot]
    exact ⟨_, rfl⟩

/-- Left-prefix synchronized-child mirror. -/
theorem
    exists_profiledRawJointHybridMegaGuardedLeftPrefixClose_sameChild
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (past : List (In₁ × In₂)) (input : In₁ × In₂)
    (nextInputOne : In₁) (nextInputTwo : In₂) :
    ∃ child outputOne owner outputTwo receiver,
      profiledRawJointHybridMegaGuardedLeftCloseOwnerOne? A strategy hwin
          initialBank
            (profiledRawJointHybridGuardedLeftPrefixReceiverAfter A strategy
              hwin installation past input) nextInputOne =
        some (outputOne, ⟨child, owner⟩) ∧
      profiledRawJointHybridMegaGuardedLeftCloseReceiverTwo? A strategy hwin
          initialBank
            (profiledRawJointHybridGuardedLeftPrefixReceiverAfter A strategy
              hwin installation past input) nextInputTwo nextInputOne =
        some (outputTwo, ⟨child, receiver⟩) := by
  rcases
      exists_profiledRawJointHybridGuardedLeftPrefixReceiverAfter_targetRoot A
        strategy hwin initialBank installation past input with
    ⟨root, hroot⟩
  rw [profiledRawJointHybridMegaGuardedLeftCloseOwnerOne?_some A strategy hwin
      initialBank _ root hroot,
    profiledRawJointHybridMegaGuardedLeftCloseReceiverTwo?_some A strategy hwin
      initialBank _ root hroot]
  exact ⟨root.1, _, _, _, _, rfl, rfl⟩

end

end DetParityAutomaton

end DistributedSynthesis
