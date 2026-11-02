/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridMegaGuardedLinkedAdapter
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridGuardedSiblingStrictTrajectory
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointIndexedPolicyRecurrentSimulation

/-!
# Reachable physical rows of the guarded mega-linked controller

These equations expose the concrete global transitions through the root,
initial-shadow handoff, and first guarded round.  They are the induction rules
used by the eventual run split; no semantic premise occurs in them.
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

private abbrev Mega (fallbackTag : RetainedTag A strategy hwin) :=
  MegaGuardedLinkedPhysicalController A strategy hwin controllers initialBank
    fallbackTag

private abbrev Child :=
  ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank

private abbrev GuardedExceptionalOne :=
  ProfiledRawJointHybridMegaGuardedLinkedExceptionalOne A strategy hwin
    controllers initialBank

private abbrev GuardedExceptionalTwo :=
  ProfiledRawJointHybridMegaGuardedLinkedExceptionalTwo A strategy hwin
    controllers initialBank

private abbrev FixedOne (child : Child A strategy hwin initialBank) :=
  ProfiledRawJointUnitPolicyOneControl A strategy
    (profiledRawJointHybridMegaChildSource A strategy hwin initialBank child)
    (profiledRawJointHybridMegaChildPolicy A strategy hwin initialBank child)
    (profiledRawJointHybridMegaChildControllerBank A strategy hwin initialBank
      child) Unit (GuardedExceptionalOne A strategy hwin controllers initialBank)

private abbrev FixedTwo (child : Child A strategy hwin initialBank) :=
  ProfiledRawJointUnitPolicyTwoControl A strategy
    (profiledRawJointHybridMegaChildSource A strategy hwin initialBank child)
    (profiledRawJointHybridMegaChildPolicy A strategy hwin initialBank child)
    (profiledRawJointHybridMegaChildControllerBank A strategy hwin initialBank
      child) Unit (GuardedExceptionalTwo A strategy hwin controllers initialBank)

/-- Canonical physical state after a nonempty guarded-right strict prefix.
The split `past`/`input` remembers the latest checked target. -/
noncomputable def profiledRawJointHybridMegaGuardedLinkedRightPrefixControls
    (fallbackTag : RetainedTag A strategy hwin)
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (outputOne : Out₁) (outputTwo : Out₂) :
    (Mega A strategy hwin controllers initialBank fallbackTag).OneControl ×
      (Mega A strategy hwin controllers initialBank fallbackTag).TwoControl :=
  ((.exceptional (.inr (.inr (.inl
      (profiledRawJointHybridGuardedRightPrefixOwner A strategy hwin
        installation (past ++ [input]))))), outputOne),
    (.exceptional (.inr (.inr (.inl
      (profiledRawJointHybridGuardedRightPrefixReceiverAfter A strategy hwin
        installation past input)))), outputTwo))

/-- Left-oriented canonical physical strict-prefix state. -/
noncomputable def profiledRawJointHybridMegaGuardedLinkedLeftPrefixControls
    (fallbackTag : RetainedTag A strategy hwin)
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (past : List (In₁ × In₂)) (input : In₁ × In₂)
    (outputOne : Out₁) (outputTwo : Out₂) :
    (Mega A strategy hwin controllers initialBank fallbackTag).OneControl ×
      (Mega A strategy hwin controllers initialBank fallbackTag).TwoControl :=
  ((.exceptional (.inr (.inr (.inr
      (profiledRawJointHybridGuardedLeftPrefixReceiverAfter A strategy hwin
        installation past input)))), outputOne),
    (.exceptional (.inr (.inr (.inr
      (profiledRawJointHybridGuardedLeftPrefixOwner A strategy hwin
        installation (past ++ [input]))))), outputTwo))

/-! ## Root and guarded installation -/

set_option maxHeartbeats 1000000 in
theorem profiledRawJointHybridMegaGuardedLinked_root_both
    (fallbackTag : RetainedTag A strategy hwin)
    (inputOne : In₁) (inputTwo : In₂) :
    let mega := Mega A strategy hwin controllers initialBank fallbackTag
    let nextOne := profiledRawJointHybridInitialRootRecvOne A strategy hwin
      controllers (inputOne, inputTwo)
    let nextTwo := profiledRawJointHybridInitialRootRecvTwo A strategy hwin
      controllers (inputOne, inputTwo)
    mega.advanceControls (mega.initialOne, mega.initialTwo)
        ⟨inputOne, inputTwo, .both⟩ =
      ((profiledRawJointHybridMegaGuardedLinkedLiftFrontOne A strategy hwin
          controllers initialBank
            (.exceptional
              (profiledRawJointHybridMegaExceptionalOneOfInitialShadow A
                strategy hwin controllers initialBank nextOne.2)), nextOne.1),
        (profiledRawJointHybridMegaGuardedLinkedLiftFrontTwo A strategy hwin
          controllers initialBank
            (.exceptional
              (profiledRawJointHybridMegaExceptionalTwoOfInitialShadow A
                strategy hwin controllers initialBank nextTwo.2)), nextTwo.1)) :=
  rfl

set_option maxHeartbeats 1000000 in
theorem profiledRawJointHybridMegaGuardedLinked_initialShadows_both
    (fallbackTag : RetainedTag A strategy hwin)
    (shadowOne : ProfiledRawJointHybridInitialOneShadow A strategy hwin
      controllers)
    (shadowTwo : ProfiledRawJointHybridInitialTwoShadow A strategy hwin
      controllers)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (inputOne : In₁) (inputTwo : In₂) :
    let mega := Mega A strategy hwin controllers initialBank fallbackTag
    let nextOne := profiledRawJointHybridMegaInitialToCoupledOne A strategy hwin
      controllers shadowTwo inputOne inputTwo
    let nextTwo := profiledRawJointHybridMegaInitialToCoupledTwo A strategy hwin
      controllers shadowOne inputTwo inputOne
    let guardedOne :=
      initialProfiledRawJointHybridGuardedCoupledOne A strategy hwin
        (.inl nextOne.2.1)
    let guardedTwo :=
      initialProfiledRawJointHybridGuardedCoupledTwo A strategy hwin
        (.inl nextTwo.2.1)
    mega.advanceControls
        ((profiledRawJointHybridMegaGuardedLinkedLiftFrontOne A strategy hwin
            controllers initialBank
              (.exceptional
                (profiledRawJointHybridMegaExceptionalOneOfInitialShadow A
                  strategy hwin controllers initialBank shadowOne)),
            oldOutputOne),
          (profiledRawJointHybridMegaGuardedLinkedLiftFrontTwo A strategy hwin
            controllers initialBank
              (.exceptional
                (profiledRawJointHybridMegaExceptionalTwoOfInitialShadow A
                  strategy hwin controllers initialBank shadowTwo)),
            oldOutputTwo))
        ⟨inputOne, inputTwo, .both⟩ =
      ((.exceptional (.inr (.inl guardedOne)), nextOne.1),
        (.exceptional (.inr (.inl guardedTwo)), nextTwo.1)) :=
  rfl

/-! ## First locally ambiguous guarded round -/

set_option maxHeartbeats 1000000 in
theorem profiledRawJointHybridMegaGuardedLinked_coupled_right
    (fallbackTag : RetainedTag A strategy hwin)
    (one : ProfiledRawJointHybridGuardedCoupledOne A strategy hwin)
    (two : ProfiledRawJointHybridGuardedCoupledTwo A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (inputOne : In₁) (inputTwo : In₂) :
    let mega := Mega A strategy hwin controllers initialBank fallbackTag
    let nextOne := startProfiledRawJointHybridGuardedRightOwner A strategy hwin
      one inputOne
    let nextTwo :=
      startProfiledRawJointHybridGuardedRightReceiver A strategy hwin one
        inputTwo inputOne
    mega.advanceControls
        ((.exceptional (.inr (.inl one)), oldOutputOne),
          (.exceptional (.inr (.inl two)), oldOutputTwo))
        ⟨inputOne, inputTwo, .right⟩ =
      ((.exceptional (.inr (.inr (.inl nextOne.2))), nextOne.1),
        (.exceptional (.inr (.inr (.inl nextTwo.2))), nextTwo.1)) :=
  rfl

set_option maxHeartbeats 1000000 in
theorem profiledRawJointHybridMegaGuardedLinked_coupled_left
    (fallbackTag : RetainedTag A strategy hwin)
    (one : ProfiledRawJointHybridGuardedCoupledOne A strategy hwin)
    (two : ProfiledRawJointHybridGuardedCoupledTwo A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (inputOne : In₁) (inputTwo : In₂) :
    let mega := Mega A strategy hwin controllers initialBank fallbackTag
    let nextOne :=
      startProfiledRawJointHybridGuardedLeftReceiver A strategy hwin two
        inputOne inputTwo
    let nextTwo := startProfiledRawJointHybridGuardedLeftOwner A strategy hwin
      two inputTwo
    mega.advanceControls
        ((.exceptional (.inr (.inl one)), oldOutputOne),
          (.exceptional (.inr (.inl two)), oldOutputTwo))
        ⟨inputOne, inputTwo, .left⟩ =
      ((.exceptional (.inr (.inr (.inr nextOne.2))), nextOne.1),
        (.exceptional (.inr (.inr (.inr nextTwo.2))), nextTwo.1)) :=
  rfl

set_option maxHeartbeats 1000000 in
theorem profiledRawJointHybridMegaGuardedLinked_coupled_both
    (fallbackTag : RetainedTag A strategy hwin)
    (one : ProfiledRawJointHybridGuardedCoupledOne A strategy hwin)
    (two : ProfiledRawJointHybridGuardedCoupledTwo A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (inputOne : In₁) (inputTwo : In₂) :
    let mega := Mega A strategy hwin controllers initialBank fallbackTag
    let nextOne :=
      startProfiledRawJointHybridGuardedLeftReceiver A strategy hwin two
        inputOne inputTwo
    let nextTwo :=
      startProfiledRawJointHybridGuardedRightReceiver A strategy hwin one
        inputTwo inputOne
    mega.advanceControls
        ((.exceptional (.inr (.inl one)), oldOutputOne),
          (.exceptional (.inr (.inl two)), oldOutputTwo))
        ⟨inputOne, inputTwo, .both⟩ =
      ((.exceptional (.inr (.inr (.inr nextOne.2))), nextOne.1),
        (.exceptional (.inr (.inr (.inl nextTwo.2))), nextTwo.1)) :=
  rfl

/-! ## Canonical finite strict blocks -/

theorem profiledRawJointHybridMegaGuardedLinked_coupled_right_prefix
    (fallbackTag : RetainedTag A strategy hwin)
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (inputOne : In₁) (inputTwo : In₂) :
    let mega := Mega A strategy hwin controllers initialBank fallbackTag
    let one := initialProfiledRawJointHybridGuardedCoupledOne A strategy hwin
      installation
    let two := initialProfiledRawJointHybridGuardedCoupledTwo A strategy hwin
      installation
    let nextOne := startProfiledRawJointHybridGuardedRightOwner A strategy hwin
      one inputOne
    let nextTwo :=
      startProfiledRawJointHybridGuardedRightReceiver A strategy hwin one
        inputTwo inputOne
    mega.advanceControls
        ((.exceptional (.inr (.inl one)), oldOutputOne),
          (.exceptional (.inr (.inl two)), oldOutputTwo))
        ⟨inputOne, inputTwo, .right⟩ =
      profiledRawJointHybridMegaGuardedLinkedRightPrefixControls A strategy
        hwin controllers initialBank fallbackTag installation []
          (inputTwo, inputOne) nextOne.1 nextTwo.1 := by
  dsimp only
  rw [profiledRawJointHybridMegaGuardedLinked_coupled_right A strategy hwin]
  simp only [profiledRawJointHybridMegaGuardedLinkedRightPrefixControls,
    List.nil_append,
    profiledRawJointHybridGuardedRight_startReceiver_eq_prefix]
  rw [profiledRawJointHybridGuardedRight_startOwner_eq_prefix A strategy hwin
    installation inputOne inputTwo]
  apply Prod.ext <;> apply Prod.ext <;> rfl

theorem profiledRawJointHybridMegaGuardedLinked_coupled_left_prefix
    (fallbackTag : RetainedTag A strategy hwin)
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (inputOne : In₁) (inputTwo : In₂) :
    let mega := Mega A strategy hwin controllers initialBank fallbackTag
    let one := initialProfiledRawJointHybridGuardedCoupledOne A strategy hwin
      installation
    let two := initialProfiledRawJointHybridGuardedCoupledTwo A strategy hwin
      installation
    let nextOne :=
      startProfiledRawJointHybridGuardedLeftReceiver A strategy hwin two
        inputOne inputTwo
    let nextTwo := startProfiledRawJointHybridGuardedLeftOwner A strategy hwin
      two inputTwo
    mega.advanceControls
        ((.exceptional (.inr (.inl one)), oldOutputOne),
          (.exceptional (.inr (.inl two)), oldOutputTwo))
        ⟨inputOne, inputTwo, .left⟩ =
      profiledRawJointHybridMegaGuardedLinkedLeftPrefixControls A strategy hwin
        controllers initialBank fallbackTag installation []
          (inputOne, inputTwo) nextOne.1 nextTwo.1 := by
  dsimp only
  rw [profiledRawJointHybridMegaGuardedLinked_coupled_left A strategy hwin]
  simp only [profiledRawJointHybridMegaGuardedLinkedLeftPrefixControls,
    List.nil_append,
    profiledRawJointHybridGuardedLeft_startReceiver_eq_prefix]
  rw [profiledRawJointHybridGuardedLeft_startOwner_eq_prefix A strategy hwin
    installation inputOne inputTwo]
  apply Prod.ext <;> apply Prod.ext <;> rfl

theorem profiledRawJointHybridMegaGuardedLinked_rightPrefix_right
    (fallbackTag : RetainedTag A strategy hwin)
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (nextInputOne : In₁) (nextInputTwo : In₂) :
    let mega := Mega A strategy hwin controllers initialBank fallbackTag
    let owner := profiledRawJointHybridGuardedRightPrefixOwner A strategy hwin
      installation (past ++ [input])
    let receiver :=
      profiledRawJointHybridGuardedRightPrefixReceiverAfter A strategy hwin
        installation past input
    let nextOwner := stepProfiledRawJointHybridGuardedRightOwner A strategy
      hwin owner nextInputOne
    let nextReceiver := stepProfiledRawJointHybridGuardedRightReceiver A
      strategy hwin receiver owner nextInputTwo nextInputOne
    mega.advanceControls
        (profiledRawJointHybridMegaGuardedLinkedRightPrefixControls A strategy
          hwin controllers initialBank fallbackTag installation past input
            oldOutputOne oldOutputTwo)
        ⟨nextInputOne, nextInputTwo, .right⟩ =
      profiledRawJointHybridMegaGuardedLinkedRightPrefixControls A strategy
        hwin controllers initialBank fallbackTag installation (past ++ [input])
          (nextInputTwo, nextInputOne) nextOwner.1 nextReceiver.1 := by
  change
    ((ProfiledRawJointLeaderFreeOneControl.exceptional (Sum.inr (Sum.inr (Sum.inl
        (stepProfiledRawJointHybridGuardedRightOwner A strategy hwin
          (profiledRawJointHybridGuardedRightPrefixOwner A strategy hwin
            installation (past ++ [input])) nextInputOne).2))),
      (stepProfiledRawJointHybridGuardedRightOwner A strategy hwin
        (profiledRawJointHybridGuardedRightPrefixOwner A strategy hwin
          installation (past ++ [input])) nextInputOne).1),
      (ProfiledRawJointLeaderFreeTwoControl.exceptional (Sum.inr (Sum.inr (Sum.inl
        (stepProfiledRawJointHybridGuardedRightReceiver A strategy hwin
          (profiledRawJointHybridGuardedRightPrefixReceiverAfter A strategy
            hwin installation past input)
          (profiledRawJointHybridGuardedRightPrefixOwner A strategy hwin
            installation (past ++ [input])) nextInputTwo nextInputOne).2))),
      (stepProfiledRawJointHybridGuardedRightReceiver A strategy hwin
        (profiledRawJointHybridGuardedRightPrefixReceiverAfter A strategy hwin
          installation past input)
        (profiledRawJointHybridGuardedRightPrefixOwner A strategy hwin
          installation (past ++ [input])) nextInputTwo nextInputOne).1))
      = _
  rw [profiledRawJointHybridGuardedRightPrefixOwner_step A strategy hwin
      installation (past ++ [input]) (nextInputTwo, nextInputOne),
    profiledRawJointHybridGuardedRightPrefixReceiverAfter_step A strategy hwin
      installation past input (nextInputTwo, nextInputOne)]
  unfold profiledRawJointHybridMegaGuardedLinkedRightPrefixControls
  rfl

theorem profiledRawJointHybridMegaGuardedLinked_leftPrefix_left
    (fallbackTag : RetainedTag A strategy hwin)
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (past : List (In₁ × In₂)) (input : In₁ × In₂)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (nextInputOne : In₁) (nextInputTwo : In₂) :
    let mega := Mega A strategy hwin controllers initialBank fallbackTag
    let receiver :=
      profiledRawJointHybridGuardedLeftPrefixReceiverAfter A strategy hwin
        installation past input
    let owner := profiledRawJointHybridGuardedLeftPrefixOwner A strategy hwin
      installation (past ++ [input])
    let nextReceiver := stepProfiledRawJointHybridGuardedLeftReceiver A
      strategy hwin receiver owner nextInputOne nextInputTwo
    let nextOwner := stepProfiledRawJointHybridGuardedLeftOwner A strategy hwin
      owner nextInputTwo
    mega.advanceControls
        (profiledRawJointHybridMegaGuardedLinkedLeftPrefixControls A strategy
          hwin controllers initialBank fallbackTag installation past input
            oldOutputOne oldOutputTwo)
        ⟨nextInputOne, nextInputTwo, .left⟩ =
      profiledRawJointHybridMegaGuardedLinkedLeftPrefixControls A strategy hwin
        controllers initialBank fallbackTag installation (past ++ [input])
          (nextInputOne, nextInputTwo) nextReceiver.1 nextOwner.1 := by
  change
    ((ProfiledRawJointLeaderFreeOneControl.exceptional (Sum.inr (Sum.inr (Sum.inr
        (stepProfiledRawJointHybridGuardedLeftReceiver A strategy hwin
          (profiledRawJointHybridGuardedLeftPrefixReceiverAfter A strategy
            hwin installation past input)
          (profiledRawJointHybridGuardedLeftPrefixOwner A strategy hwin
            installation (past ++ [input])) nextInputOne nextInputTwo).2))),
      (stepProfiledRawJointHybridGuardedLeftReceiver A strategy hwin
        (profiledRawJointHybridGuardedLeftPrefixReceiverAfter A strategy hwin
          installation past input)
        (profiledRawJointHybridGuardedLeftPrefixOwner A strategy hwin
          installation (past ++ [input])) nextInputOne nextInputTwo).1),
      (ProfiledRawJointLeaderFreeTwoControl.exceptional (Sum.inr (Sum.inr (Sum.inr
        (stepProfiledRawJointHybridGuardedLeftOwner A strategy hwin
          (profiledRawJointHybridGuardedLeftPrefixOwner A strategy hwin
            installation (past ++ [input])) nextInputTwo).2))),
      (stepProfiledRawJointHybridGuardedLeftOwner A strategy hwin
        (profiledRawJointHybridGuardedLeftPrefixOwner A strategy hwin
          installation (past ++ [input])) nextInputTwo).1)) = _
  rw [profiledRawJointHybridGuardedLeftPrefixReceiverAfter_step A strategy hwin
      installation past input (nextInputOne, nextInputTwo),
    profiledRawJointHybridGuardedLeftPrefixOwner_step A strategy hwin
      installation (past ++ [input]) (nextInputOne, nextInputTwo)]
  unfold profiledRawJointHybridMegaGuardedLinkedLeftPrefixControls
  rfl

/-! ## First simultaneous round after a strict prefix -/

/-- The first simultaneous round after a guarded-right strict prefix does not
yet enter the recurrent receiver cross.  Process one closes the old checked
root through its honest `.first` coordinate, while process two advances the
guarded-right receiver and thereby refreshes the target for the current
simultaneous occurrence.  The result is the mixed state consumed by the
repeated-simultaneous handoff below. -/
theorem
    profiledRawJointHybridMegaGuardedLinked_rightPrefix_firstBoth_mixed
    (fallbackTag : RetainedTag A strategy hwin)
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (nextInputOne : In₁) (nextInputTwo : In₂)
    (root : ProfiledRawJointHybridMegaGuardedRightTargetRoot A strategy hwin
      initialBank)
    (hroot :
      profiledRawJointHybridGuardedRightReceiverTargetRoot? A strategy hwin
          initialBank
          (profiledRawJointHybridGuardedRightPrefixReceiverAfter A strategy
            hwin installation past input) = some root) :
    let mega := Mega A strategy hwin controllers initialBank fallbackTag
    let source := profiledRawJointHybridMegaChildSource A strategy hwin
      initialBank root.1
    let policy := profiledRawJointHybridMegaChildPolicy A strategy hwin
      initialBank root.1
    let bank := profiledRawJointHybridMegaChildControllerBank A strategy hwin
      initialBank root.1
    let restart := profiledRawJointUnitRestartLeft A strategy source policy
      bank root.2 .first
    let nextLeft := continueProfiledRawJointUnitLeftPolicyReceiver A strategy
      source policy bank restart.2 restart.1 (nextInputOne, nextInputTwo)
    let nextRight := stepProfiledRawJointHybridGuardedRightReceiver A strategy
      hwin
      (profiledRawJointHybridGuardedRightPrefixReceiverAfter A strategy hwin
        installation past input)
      (profiledRawJointHybridGuardedRightPrefixOwner A strategy hwin
        installation (past ++ [input])) nextInputTwo nextInputOne
    mega.advanceControls
        (profiledRawJointHybridMegaGuardedLinkedRightPrefixControls A strategy
          hwin controllers initialBank fallbackTag installation past input
            oldOutputOne oldOutputTwo)
        ⟨nextInputOne, nextInputTwo, .both⟩ =
      ((.leftReceiver root.1 nextLeft.2, nextLeft.1),
        (.exceptional (.inr (.inr (.inl
          (profiledRawJointHybridGuardedRightPrefixReceiverAfter A strategy
            hwin installation (past ++ [input])
              (nextInputTwo, nextInputOne))))), nextRight.1)) := by
  dsimp only
  let state :=
    profiledRawJointHybridGuardedRightPrefixReceiverAfter A strategy hwin
      installation past input
  let owner := profiledRawJointHybridGuardedRightPrefixOwner A strategy hwin
    installation (past ++ [input])
  let source := profiledRawJointHybridMegaChildSource A strategy hwin
    initialBank root.1
  let policy := profiledRawJointHybridMegaChildPolicy A strategy hwin
    initialBank root.1
  let bank := profiledRawJointHybridMegaChildControllerBank A strategy hwin
    initialBank root.1
  let restart := profiledRawJointUnitRestartLeft A strategy source policy bank
    root.2 .first
  let nextLeft := continueProfiledRawJointUnitLeftPolicyReceiver A strategy
    source policy bank restart.2 restart.1 (nextInputOne, nextInputTwo)
  let nextRight := stepProfiledRawJointHybridGuardedRightReceiver A strategy
    hwin state owner nextInputTwo nextInputOne
  have hclose :=
    profiledRawJointHybridMegaGuardedRightCloseReceiverOne?_some A strategy
      hwin initialBank state root hroot nextInputOne nextInputTwo
  have hone :
      (profiledRawJointHybridMegaGuardedLinkedExceptionalAdapter A strategy
        hwin controllers initialBank fallbackTag).otherRecvOne
          (.exceptional (.inr (.inr (.inl owner)))) nextInputOne
          (.exceptional (.inr (.inr (.inl state)))) nextInputTwo =
        (nextLeft.1, .leftReceiver root.1 nextLeft.2) := by
    change
      (match
          profiledRawJointHybridMegaGuardedRightCloseReceiverOne? A strategy
            hwin initialBank state nextInputOne nextInputTwo with
        | none => _
        | some installed =>
            (installed.1,
              ProfiledRawJointLeaderFreeOneControl.leftReceiver installed.2.1
                installed.2.2)) = _
    rw [hclose]
  have htwo :
      (profiledRawJointHybridMegaGuardedLinkedExceptionalAdapter A strategy
        hwin controllers initialBank fallbackTag).otherRecvTwo
          (.exceptional (.inr (.inr (.inl state)))) nextInputTwo
          (.exceptional (.inr (.inr (.inl owner)))) nextInputOne =
        (nextRight.1,
          .exceptional (.inr (.inr (.inl nextRight.2)))) := by
    rfl
  apply Prod.ext
  · change
      (((profiledRawJointHybridMegaGuardedLinkedExceptionalAdapter A strategy
        hwin controllers initialBank fallbackTag).otherRecvOne
          (.exceptional (.inr (.inr (.inl owner)))) nextInputOne
          (.exceptional (.inr (.inr (.inl state)))) nextInputTwo).2,
        ((profiledRawJointHybridMegaGuardedLinkedExceptionalAdapter A strategy
        hwin controllers initialBank fallbackTag).otherRecvOne
          (.exceptional (.inr (.inr (.inl owner)))) nextInputOne
          (.exceptional (.inr (.inr (.inl state)))) nextInputTwo).1) = _
    rw [hone]
  · change
      (((profiledRawJointHybridMegaGuardedLinkedExceptionalAdapter A strategy
        hwin controllers initialBank fallbackTag).otherRecvTwo
          (.exceptional (.inr (.inr (.inl state)))) nextInputTwo
          (.exceptional (.inr (.inr (.inl owner)))) nextInputOne).2,
        ((profiledRawJointHybridMegaGuardedLinkedExceptionalAdapter A strategy
        hwin controllers initialBank fallbackTag).otherRecvTwo
          (.exceptional (.inr (.inr (.inl state)))) nextInputTwo
          (.exceptional (.inr (.inr (.inl owner)))) nextInputOne).1) = _
    rw [htwo,
      profiledRawJointHybridGuardedRightPrefixReceiverAfter_step A strategy
        hwin installation past input (nextInputTwo, nextInputOne)]

/-- Guarded-left mirror of the first-simultaneous mixed-state equation. -/
theorem
    profiledRawJointHybridMegaGuardedLinked_leftPrefix_firstBoth_mixed
    (fallbackTag : RetainedTag A strategy hwin)
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (past : List (In₁ × In₂)) (input : In₁ × In₂)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (nextInputOne : In₁) (nextInputTwo : In₂)
    (root : ProfiledRawJointHybridMegaGuardedLeftTargetRoot A strategy hwin
      initialBank)
    (hroot :
      profiledRawJointHybridGuardedLeftReceiverTargetRoot? A strategy hwin
          initialBank
          (profiledRawJointHybridGuardedLeftPrefixReceiverAfter A strategy
            hwin installation past input) = some root) :
    let mega := Mega A strategy hwin controllers initialBank fallbackTag
    let nextLeft := stepProfiledRawJointHybridGuardedLeftReceiver A strategy
      hwin
      (profiledRawJointHybridGuardedLeftPrefixReceiverAfter A strategy hwin
        installation past input)
      (profiledRawJointHybridGuardedLeftPrefixOwner A strategy hwin
        installation (past ++ [input])) nextInputOne nextInputTwo
    let source := profiledRawJointHybridMegaChildSource A strategy hwin
      initialBank root.1
    let policy := profiledRawJointHybridMegaChildPolicy A strategy hwin
      initialBank root.1
    let bank := profiledRawJointHybridMegaChildControllerBank A strategy hwin
      initialBank root.1
    let restart := profiledRawJointUnitRestartRight A strategy source policy
      bank root.2 .first
    let nextRight := continueProfiledRawJointUnitRightPolicyReceiver A strategy
      source policy bank restart.2 restart.1 (nextInputTwo, nextInputOne)
    mega.advanceControls
        (profiledRawJointHybridMegaGuardedLinkedLeftPrefixControls A strategy
          hwin controllers initialBank fallbackTag installation past input
            oldOutputOne oldOutputTwo)
        ⟨nextInputOne, nextInputTwo, .both⟩ =
      ((.exceptional (.inr (.inr (.inr
          (profiledRawJointHybridGuardedLeftPrefixReceiverAfter A strategy
            hwin installation (past ++ [input])
              (nextInputOne, nextInputTwo))))), nextLeft.1),
        (.rightReceiver root.1 nextRight.2, nextRight.1)) := by
  dsimp only
  let state :=
    profiledRawJointHybridGuardedLeftPrefixReceiverAfter A strategy hwin
      installation past input
  let owner := profiledRawJointHybridGuardedLeftPrefixOwner A strategy hwin
    installation (past ++ [input])
  let nextLeft := stepProfiledRawJointHybridGuardedLeftReceiver A strategy
    hwin state owner nextInputOne nextInputTwo
  let source := profiledRawJointHybridMegaChildSource A strategy hwin
    initialBank root.1
  let policy := profiledRawJointHybridMegaChildPolicy A strategy hwin
    initialBank root.1
  let bank := profiledRawJointHybridMegaChildControllerBank A strategy hwin
    initialBank root.1
  let restart := profiledRawJointUnitRestartRight A strategy source policy bank
    root.2 .first
  let nextRight := continueProfiledRawJointUnitRightPolicyReceiver A strategy
    source policy bank restart.2 restart.1 (nextInputTwo, nextInputOne)
  have hclose :=
    profiledRawJointHybridMegaGuardedLeftCloseReceiverTwo?_some A strategy hwin
      initialBank state root hroot nextInputTwo nextInputOne
  have hone :
      (profiledRawJointHybridMegaGuardedLinkedExceptionalAdapter A strategy
        hwin controllers initialBank fallbackTag).otherRecvOne
          (.exceptional (.inr (.inr (.inr state)))) nextInputOne
          (.exceptional (.inr (.inr (.inr owner)))) nextInputTwo =
        (nextLeft.1,
          .exceptional (.inr (.inr (.inr nextLeft.2)))) := by
    rfl
  have htwo :
      (profiledRawJointHybridMegaGuardedLinkedExceptionalAdapter A strategy
        hwin controllers initialBank fallbackTag).otherRecvTwo
          (.exceptional (.inr (.inr (.inr owner)))) nextInputTwo
          (.exceptional (.inr (.inr (.inr state)))) nextInputOne =
        (nextRight.1, .rightReceiver root.1 nextRight.2) := by
    change
      (match
          profiledRawJointHybridMegaGuardedLeftCloseReceiverTwo? A strategy
            hwin initialBank state nextInputTwo nextInputOne with
        | none => _
        | some installed =>
            (installed.1,
              ProfiledRawJointLeaderFreeTwoControl.rightReceiver installed.2.1
                installed.2.2)) = _
    rw [hclose]
  apply Prod.ext
  · change
      (((profiledRawJointHybridMegaGuardedLinkedExceptionalAdapter A strategy
        hwin controllers initialBank fallbackTag).otherRecvOne
          (.exceptional (.inr (.inr (.inr state)))) nextInputOne
          (.exceptional (.inr (.inr (.inr owner)))) nextInputTwo).2,
        ((profiledRawJointHybridMegaGuardedLinkedExceptionalAdapter A strategy
        hwin controllers initialBank fallbackTag).otherRecvOne
          (.exceptional (.inr (.inr (.inr state)))) nextInputOne
          (.exceptional (.inr (.inr (.inr owner)))) nextInputTwo).1) = _
    rw [hone,
      profiledRawJointHybridGuardedLeftPrefixReceiverAfter_step A strategy
        hwin installation past input (nextInputOne, nextInputTwo)]
  · change
      (((profiledRawJointHybridMegaGuardedLinkedExceptionalAdapter A strategy
        hwin controllers initialBank fallbackTag).otherRecvTwo
          (.exceptional (.inr (.inr (.inr owner)))) nextInputTwo
          (.exceptional (.inr (.inr (.inr state)))) nextInputOne).2,
        ((profiledRawJointHybridMegaGuardedLinkedExceptionalAdapter A strategy
        hwin controllers initialBank fallbackTag).otherRecvTwo
          (.exceptional (.inr (.inr (.inr owner)))) nextInputTwo
          (.exceptional (.inr (.inr (.inr state)))) nextInputOne).1) = _
    rw [htwo]

/-- The guarded receiver installed by the first simultaneous round has a
successful root lookup for the refreshed current occurrence. -/
theorem
    exists_profiledRawJointHybridMegaGuardedLinked_rightPrefix_firstBoth_refreshedRoot
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (nextInputOne : In₁) (nextInputTwo : In₂) :
    ∃ root : ProfiledRawJointHybridMegaGuardedRightTargetRoot A strategy hwin
        initialBank,
      profiledRawJointHybridGuardedRightReceiverTargetRoot? A strategy hwin
          initialBank
          (profiledRawJointHybridGuardedRightPrefixReceiverAfter A strategy
            hwin installation (past ++ [input])
              (nextInputTwo, nextInputOne)) = some root :=
  exists_profiledRawJointHybridGuardedRightPrefixReceiverAfter_targetRoot A
    strategy hwin initialBank installation (past ++ [input])
      (nextInputTwo, nextInputOne)

/-- Refreshed-root existence in the guarded-left orientation. -/
theorem
    exists_profiledRawJointHybridMegaGuardedLinked_leftPrefix_firstBoth_refreshedRoot
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (past : List (In₁ × In₂)) (input : In₁ × In₂)
    (nextInputOne : In₁) (nextInputTwo : In₂) :
    ∃ root : ProfiledRawJointHybridMegaGuardedLeftTargetRoot A strategy hwin
        initialBank,
      profiledRawJointHybridGuardedLeftReceiverTargetRoot? A strategy hwin
          initialBank
          (profiledRawJointHybridGuardedLeftPrefixReceiverAfter A strategy
            hwin installation (past ++ [input])
              (nextInputOne, nextInputTwo)) = some root :=
  exists_profiledRawJointHybridGuardedLeftPrefixReceiverAfter_targetRoot A
    strategy hwin initialBank installation (past ++ [input])
      (nextInputOne, nextInputTwo)

/-! ## Certified strict reversal into one indexed child -/

/-- On a repeated simultaneous round, both local receive maps choose the
guarded-right checked target as their immutable anchor.  Hence they enter one
ordinary receiver/receiver cross at a literal common mega child. -/
theorem
    exists_profiledRawJointHybridMegaGuardedLinked_rightPrefix_bothClose
    (fallbackTag : RetainedTag A strategy hwin)
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (leftReceiver :
      ProfiledRawJointHybridGuardedLeftInstalledReceiver A strategy hwin)
    (nextInputOne : In₁) (nextInputTwo : In₂) :
    ∃ child outputOne nextLeft outputTwo nextRight,
      (profiledRawJointHybridMegaGuardedLinkedExceptionalAdapter A strategy
        hwin controllers initialBank fallbackTag).otherRecvOne
          (.exceptional (.inr (.inr (.inr leftReceiver)))) nextInputOne
          (.exceptional (.inr (.inr (.inl
            (profiledRawJointHybridGuardedRightPrefixReceiverAfter A strategy
              hwin installation past input))))) nextInputTwo =
        (outputOne, .leftReceiver child nextLeft) ∧
      (profiledRawJointHybridMegaGuardedLinkedExceptionalAdapter A strategy
        hwin controllers initialBank fallbackTag).otherRecvTwo
          (.exceptional (.inr (.inr (.inl
            (profiledRawJointHybridGuardedRightPrefixReceiverAfter A strategy
              hwin installation past input))))) nextInputTwo
          (.exceptional (.inr (.inr (.inr leftReceiver)))) nextInputOne =
        (outputTwo, .rightReceiver child nextRight) := by
  rcases
      exists_profiledRawJointHybridMegaGuardedRightPrefixCloseBoth_sameChild A
        strategy hwin initialBank installation past input nextInputOne
          nextInputTwo with
    ⟨child, outputOne, nextLeft, outputTwo, nextRight, hone, htwo⟩
  refine ⟨child, outputOne, nextLeft, outputTwo, nextRight, ?_, ?_⟩
  · change
      (match
          profiledRawJointHybridMegaGuardedRightCloseReceiverOneBoth? A
            strategy hwin initialBank
              (profiledRawJointHybridGuardedRightPrefixReceiverAfter A
                strategy hwin installation past input) nextInputOne
                nextInputTwo with
        | none => _
        | some installed =>
            (installed.1,
              ProfiledRawJointLeaderFreeOneControl.leftReceiver installed.2.1
                installed.2.2)) = _
    rw [hone]
  · change
      (match
          profiledRawJointHybridMegaGuardedRightCloseReceiverTwoBoth? A
            strategy hwin initialBank
              (profiledRawJointHybridGuardedRightPrefixReceiverAfter A
                strategy hwin installation past input) nextInputTwo
                nextInputOne with
        | none => _
        | some installed =>
            (installed.1,
              ProfiledRawJointLeaderFreeTwoControl.rightReceiver installed.2.1
                installed.2.2)) = _
    rw [htwo]

/-- After any certified guarded-right prefix, the two local `.left` rows
install ordinary recurrent controls under one identical child key. -/
theorem
    exists_profiledRawJointHybridMegaGuardedLinked_rightPrefix_leftClose
    (fallbackTag : RetainedTag A strategy hwin)
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (rightOwner :
      ProfiledRawJointHybridGuardedRightInstalledOwner A strategy hwin)
    (nextInputOne : In₁) (nextInputTwo : In₂) :
    ∃ child outputOne receiver outputTwo owner,
      (profiledRawJointHybridMegaGuardedLinkedExceptionalAdapter A strategy
        hwin controllers initialBank fallbackTag).otherRecvOne
          (.exceptional (.inr (.inr (.inl rightOwner)))) nextInputOne
          (.exceptional (.inr (.inr (.inl
            (profiledRawJointHybridGuardedRightPrefixReceiverAfter A strategy
              hwin installation past input))))) nextInputTwo =
        (outputOne, .leftReceiver child receiver) ∧
      (profiledRawJointHybridMegaGuardedLinkedExceptionalAdapter A strategy
        hwin controllers initialBank fallbackTag).exceptionalNoRecvTwo
          (.inr (.inr (.inl
            (profiledRawJointHybridGuardedRightPrefixReceiverAfter A strategy
              hwin installation past input)))) nextInputTwo =
        (outputTwo, .leftOwner child owner) := by
  rcases
      exists_profiledRawJointHybridMegaGuardedRightPrefixClose_sameChild A
        strategy hwin initialBank installation past input nextInputOne
          nextInputTwo with
    ⟨child, outputOne, receiver, outputTwo, owner, hone, htwo⟩
  refine ⟨child, outputOne, receiver, outputTwo, owner, ?_, ?_⟩
  · change
      (match
          profiledRawJointHybridMegaGuardedRightCloseReceiverOne? A strategy
            hwin initialBank
              (profiledRawJointHybridGuardedRightPrefixReceiverAfter A
                strategy hwin installation past input) nextInputOne
                nextInputTwo with
        | none => _
        | some installed =>
            (installed.1,
              ProfiledRawJointLeaderFreeOneControl.leftReceiver installed.2.1
                installed.2.2)) = _
    rw [hone]
  · change
      (match
          profiledRawJointHybridMegaGuardedRightCloseOwnerTwo? A strategy hwin
            initialBank
              (profiledRawJointHybridGuardedRightPrefixReceiverAfter A
                strategy hwin installation past input) nextInputTwo with
        | none => _
        | some installed =>
            (installed.1,
              ProfiledRawJointLeaderFreeTwoControl.leftOwner installed.2.1
                installed.2.2)) = _
    rw [htwo]

/-- Guarded-left strict reversal mirror. -/
theorem
    exists_profiledRawJointHybridMegaGuardedLinked_leftPrefix_rightClose
    (fallbackTag : RetainedTag A strategy hwin)
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (past : List (In₁ × In₂)) (input : In₁ × In₂)
    (leftOwner :
      ProfiledRawJointHybridGuardedLeftInstalledOwner A strategy hwin)
    (nextInputOne : In₁) (nextInputTwo : In₂) :
    ∃ child outputOne owner outputTwo receiver,
      (profiledRawJointHybridMegaGuardedLinkedExceptionalAdapter A strategy
        hwin controllers initialBank fallbackTag).exceptionalNoRecvOne
          (.inr (.inr (.inr
            (profiledRawJointHybridGuardedLeftPrefixReceiverAfter A strategy
              hwin installation past input)))) nextInputOne =
        (outputOne, .rightOwner child owner) ∧
      (profiledRawJointHybridMegaGuardedLinkedExceptionalAdapter A strategy
        hwin controllers initialBank fallbackTag).otherRecvTwo
          (.exceptional (.inr (.inr (.inr leftOwner)))) nextInputTwo
          (.exceptional (.inr (.inr (.inr
            (profiledRawJointHybridGuardedLeftPrefixReceiverAfter A strategy
              hwin installation past input))))) nextInputOne =
        (outputTwo, .rightReceiver child receiver) := by
  rcases
      exists_profiledRawJointHybridMegaGuardedLeftPrefixClose_sameChild A
        strategy hwin initialBank installation past input nextInputOne
          nextInputTwo with
    ⟨child, outputOne, owner, outputTwo, receiver, hone, htwo⟩
  refine ⟨child, outputOne, owner, outputTwo, receiver, ?_, ?_⟩
  · change
      (match
          profiledRawJointHybridMegaGuardedLeftCloseOwnerOne? A strategy hwin
            initialBank
              (profiledRawJointHybridGuardedLeftPrefixReceiverAfter A strategy
                hwin installation past input) nextInputOne with
        | none => _
        | some installed =>
            (installed.1,
              ProfiledRawJointLeaderFreeOneControl.rightOwner installed.2.1
                installed.2.2)) = _
    rw [hone]
  · change
      (match
          profiledRawJointHybridMegaGuardedLeftCloseReceiverTwo? A strategy
            hwin initialBank
              (profiledRawJointHybridGuardedLeftPrefixReceiverAfter A strategy
                hwin installation past input) nextInputTwo nextInputOne with
        | none => _
        | some installed =>
            (installed.1,
              ProfiledRawJointLeaderFreeTwoControl.rightReceiver installed.2.1
                installed.2.2)) = _
    rw [htwo]

/-! ## Literal physical reversal rows -/

/-- Literal physical form of the deterministic repeated-simultaneous close. -/
theorem
    exists_profiledRawJointHybridMegaGuardedLinked_rightPrefix_bothClose_physical
    (fallbackTag : RetainedTag A strategy hwin)
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (leftReceiver :
      ProfiledRawJointHybridGuardedLeftInstalledReceiver A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (nextInputOne : In₁) (nextInputTwo : In₂) :
    ∃ child outputOne nextLeft outputTwo nextRight,
      let mega := Mega A strategy hwin controllers initialBank fallbackTag
      mega.advanceControls
          ((.exceptional (.inr (.inr (.inr leftReceiver))), oldOutputOne),
            (.exceptional (.inr (.inr (.inl
              (profiledRawJointHybridGuardedRightPrefixReceiverAfter A
                strategy hwin installation past input)))), oldOutputTwo))
          ⟨nextInputOne, nextInputTwo, .both⟩ =
        ((.leftReceiver child nextLeft, outputOne),
          (.rightReceiver child nextRight, outputTwo)) := by
  rcases
      exists_profiledRawJointHybridMegaGuardedLinked_rightPrefix_bothClose A
        strategy hwin controllers initialBank fallbackTag installation past
          input leftReceiver nextInputOne nextInputTwo with
    ⟨child, outputOne, nextLeft, outputTwo, nextRight, hone, htwo⟩
  refine ⟨child, outputOne, nextLeft, outputTwo, nextRight, ?_⟩
  apply Prod.ext
  · change
      (((profiledRawJointHybridMegaGuardedLinkedExceptionalAdapter A strategy
          hwin controllers initialBank fallbackTag).otherRecvOne
        (.exceptional (.inr (.inr (.inr leftReceiver)))) nextInputOne
        (.exceptional (.inr (.inr (.inl
          (profiledRawJointHybridGuardedRightPrefixReceiverAfter A strategy
            hwin installation past input))))) nextInputTwo).2,
        ((profiledRawJointHybridMegaGuardedLinkedExceptionalAdapter A strategy
          hwin controllers initialBank fallbackTag).otherRecvOne
        (.exceptional (.inr (.inr (.inr leftReceiver)))) nextInputOne
        (.exceptional (.inr (.inr (.inl
          (profiledRawJointHybridGuardedRightPrefixReceiverAfter A strategy
            hwin installation past input))))) nextInputTwo).1) = _
    rw [hone]
  · change
      (((profiledRawJointHybridMegaGuardedLinkedExceptionalAdapter A strategy
          hwin controllers initialBank fallbackTag).otherRecvTwo
        (.exceptional (.inr (.inr (.inl
          (profiledRawJointHybridGuardedRightPrefixReceiverAfter A strategy
            hwin installation past input))))) nextInputTwo
        (.exceptional (.inr (.inr (.inr leftReceiver)))) nextInputOne).2,
        ((profiledRawJointHybridMegaGuardedLinkedExceptionalAdapter A strategy
          hwin controllers initialBank fallbackTag).otherRecvTwo
        (.exceptional (.inr (.inr (.inl
          (profiledRawJointHybridGuardedRightPrefixReceiverAfter A strategy
            hwin installation past input))))) nextInputTwo
        (.exceptional (.inr (.inr (.inr leftReceiver)))) nextInputOne).1) = _
    rw [htwo]

/-- The adapter-level guarded-right close is exactly the simultaneous global
physical update on a `.left` reversal.  In particular, both post-round local
controls carry the same indexed child. -/
theorem
    exists_profiledRawJointHybridMegaGuardedLinked_rightPrefix_leftClose_physical
    (fallbackTag : RetainedTag A strategy hwin)
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (rightOwner :
      ProfiledRawJointHybridGuardedRightInstalledOwner A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (nextInputOne : In₁) (nextInputTwo : In₂) :
    ∃ child outputOne receiver outputTwo owner,
      let mega := Mega A strategy hwin controllers initialBank fallbackTag
      mega.advanceControls
          ((.exceptional (.inr (.inr (.inl rightOwner))), oldOutputOne),
            (.exceptional (.inr (.inr (.inl
              (profiledRawJointHybridGuardedRightPrefixReceiverAfter A
                strategy hwin installation past input)))), oldOutputTwo))
          ⟨nextInputOne, nextInputTwo, .left⟩ =
        ((.leftReceiver child receiver, outputOne),
          (.leftOwner child owner, outputTwo)) := by
  rcases
      exists_profiledRawJointHybridMegaGuardedLinked_rightPrefix_leftClose A
        strategy hwin controllers initialBank fallbackTag installation past
          input rightOwner nextInputOne nextInputTwo with
    ⟨child, outputOne, receiver, outputTwo, owner, hone, htwo⟩
  refine ⟨child, outputOne, receiver, outputTwo, owner, ?_⟩
  apply Prod.ext
  · change
      (((profiledRawJointHybridMegaGuardedLinkedExceptionalAdapter A strategy
          hwin controllers initialBank fallbackTag).otherRecvOne
        (.exceptional (.inr (.inr (.inl rightOwner)))) nextInputOne
        (.exceptional (.inr (.inr (.inl
          (profiledRawJointHybridGuardedRightPrefixReceiverAfter A strategy
            hwin installation past input))))) nextInputTwo).2,
        ((profiledRawJointHybridMegaGuardedLinkedExceptionalAdapter A strategy
          hwin controllers initialBank fallbackTag).otherRecvOne
        (.exceptional (.inr (.inr (.inl rightOwner)))) nextInputOne
        (.exceptional (.inr (.inr (.inl
          (profiledRawJointHybridGuardedRightPrefixReceiverAfter A strategy
            hwin installation past input))))) nextInputTwo).1) = _
    rw [hone]
  · change
      (((profiledRawJointHybridMegaGuardedLinkedExceptionalAdapter A strategy
          hwin controllers initialBank fallbackTag).exceptionalNoRecvTwo
        (.inr (.inr (.inl
          (profiledRawJointHybridGuardedRightPrefixReceiverAfter A strategy
            hwin installation past input)))) nextInputTwo).2,
        ((profiledRawJointHybridMegaGuardedLinkedExceptionalAdapter A strategy
          hwin controllers initialBank fallbackTag).exceptionalNoRecvTwo
        (.inr (.inr (.inl
          (profiledRawJointHybridGuardedRightPrefixReceiverAfter A strategy
            hwin installation past input)))) nextInputTwo).1) = _
    rw [htwo]

/-- Literal physical mirror for a guarded-left prefix followed by `.right`. -/
theorem
    exists_profiledRawJointHybridMegaGuardedLinked_leftPrefix_rightClose_physical
    (fallbackTag : RetainedTag A strategy hwin)
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (past : List (In₁ × In₂)) (input : In₁ × In₂)
    (leftOwner :
      ProfiledRawJointHybridGuardedLeftInstalledOwner A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (nextInputOne : In₁) (nextInputTwo : In₂) :
    ∃ child outputOne owner outputTwo receiver,
      let mega := Mega A strategy hwin controllers initialBank fallbackTag
      mega.advanceControls
          ((.exceptional (.inr (.inr (.inr
              (profiledRawJointHybridGuardedLeftPrefixReceiverAfter A strategy
                hwin installation past input)))), oldOutputOne),
            (.exceptional (.inr (.inr (.inr leftOwner))), oldOutputTwo))
          ⟨nextInputOne, nextInputTwo, .right⟩ =
        ((.rightOwner child owner, outputOne),
          (.rightReceiver child receiver, outputTwo)) := by
  rcases
      exists_profiledRawJointHybridMegaGuardedLinked_leftPrefix_rightClose A
        strategy hwin controllers initialBank fallbackTag installation past
          input leftOwner nextInputOne nextInputTwo with
    ⟨child, outputOne, owner, outputTwo, receiver, hone, htwo⟩
  refine ⟨child, outputOne, owner, outputTwo, receiver, ?_⟩
  apply Prod.ext
  · change
      (((profiledRawJointHybridMegaGuardedLinkedExceptionalAdapter A strategy
          hwin controllers initialBank fallbackTag).exceptionalNoRecvOne
        (.inr (.inr (.inr
          (profiledRawJointHybridGuardedLeftPrefixReceiverAfter A strategy
            hwin installation past input)))) nextInputOne).2,
        ((profiledRawJointHybridMegaGuardedLinkedExceptionalAdapter A strategy
          hwin controllers initialBank fallbackTag).exceptionalNoRecvOne
        (.inr (.inr (.inr
          (profiledRawJointHybridGuardedLeftPrefixReceiverAfter A strategy
            hwin installation past input)))) nextInputOne).1) = _
    rw [hone]
  · change
      (((profiledRawJointHybridMegaGuardedLinkedExceptionalAdapter A strategy
          hwin controllers initialBank fallbackTag).otherRecvTwo
        (.exceptional (.inr (.inr (.inr leftOwner)))) nextInputTwo
        (.exceptional (.inr (.inr (.inr
          (profiledRawJointHybridGuardedLeftPrefixReceiverAfter A strategy
            hwin installation past input))))) nextInputOne).2,
        ((profiledRawJointHybridMegaGuardedLinkedExceptionalAdapter A strategy
          hwin controllers initialBank fallbackTag).otherRecvTwo
        (.exceptional (.inr (.inr (.inr leftOwner)))) nextInputTwo
        (.exceptional (.inr (.inr (.inr
          (profiledRawJointHybridGuardedLeftPrefixReceiverAfter A strategy
            hwin installation past input))))) nextInputOne).1) = _
    rw [htwo]

/-! ## Canonical recurrent handoff -/

/-- A repeated simultaneous round exits the mixed guarded receivers into the
receiver/receiver recurrent state at one common child key. -/
theorem
    exists_profiledRawJointHybridMegaGuardedLinked_rightPrefix_bothClose_recurrentAt
    (fallbackTag : RetainedTag A strategy hwin)
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (leftReceiver :
      ProfiledRawJointHybridGuardedLeftInstalledReceiver A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (nextInputOne : In₁) (nextInputTwo : In₂) :
    ∃ child, ∃ unitState :
        (FixedOne A strategy hwin controllers initialBank child × Out₁) ×
          (FixedTwo A strategy hwin controllers initialBank child × Out₂),
      ProfiledRawJointIndexedPolicyRecurrentAt A strategy
        (Child A strategy hwin initialBank)
        (profiledRawJointHybridMegaChildSource A strategy hwin initialBank)
        (profiledRawJointHybridMegaChildPolicy A strategy hwin initialBank)
        (profiledRawJointHybridMegaChildControllerBank A strategy hwin
          initialBank)
        Unit Unit
        (GuardedExceptionalOne A strategy hwin controllers initialBank)
        (GuardedExceptionalTwo A strategy hwin controllers initialBank) child
        ((Mega A strategy hwin controllers initialBank fallbackTag
          ).advanceControls
            ((.exceptional (.inr (.inr (.inr leftReceiver))), oldOutputOne),
              (.exceptional (.inr (.inr (.inl
                (profiledRawJointHybridGuardedRightPrefixReceiverAfter A
                  strategy hwin installation past input)))), oldOutputTwo))
            ⟨nextInputOne, nextInputTwo, .both⟩)
        unitState := by
  rcases
      exists_profiledRawJointHybridMegaGuardedLinked_rightPrefix_bothClose_physical
        A strategy hwin controllers initialBank fallbackTag installation past
          input leftReceiver oldOutputOne oldOutputTwo nextInputOne nextInputTwo
      with ⟨child, outputOne, left, outputTwo, right, hclose⟩
  refine ⟨child,
    (((ProfiledRawJointLeaderFreeOneControl.leftReceiver () left), outputOne),
      ((ProfiledRawJointLeaderFreeTwoControl.rightReceiver () right),
        outputTwo)), ?_⟩
  rw [hclose]
  exact .cross left right outputOne outputTwo

/-- A canonical guarded-right prefix closes physically into one matched-left
indexed state. -/
theorem
    exists_profiledRawJointHybridMegaGuardedLinked_rightPrefixControls_leftClose
    (fallbackTag : RetainedTag A strategy hwin)
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (nextInputOne : In₁) (nextInputTwo : In₂) :
    ∃ child outputOne receiver outputTwo owner,
      let mega := Mega A strategy hwin controllers initialBank fallbackTag
      mega.advanceControls
          (profiledRawJointHybridMegaGuardedLinkedRightPrefixControls A
            strategy hwin controllers initialBank fallbackTag installation
              past input oldOutputOne oldOutputTwo)
          ⟨nextInputOne, nextInputTwo, .left⟩ =
        ((.leftReceiver child receiver, outputOne),
          (.leftOwner child owner, outputTwo)) := by
  simpa only [profiledRawJointHybridMegaGuardedLinkedRightPrefixControls] using
    (exists_profiledRawJointHybridMegaGuardedLinked_rightPrefix_leftClose_physical
      A strategy hwin controllers initialBank fallbackTag installation past
        input
        (profiledRawJointHybridGuardedRightPrefixOwner A strategy hwin
          installation (past ++ [input])) oldOutputOne oldOutputTwo
            nextInputOne nextInputTwo)

/-- Canonical guarded-left mirror. -/
theorem
    exists_profiledRawJointHybridMegaGuardedLinked_leftPrefixControls_rightClose
    (fallbackTag : RetainedTag A strategy hwin)
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (past : List (In₁ × In₂)) (input : In₁ × In₂)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (nextInputOne : In₁) (nextInputTwo : In₂) :
    ∃ child outputOne owner outputTwo receiver,
      let mega := Mega A strategy hwin controllers initialBank fallbackTag
      mega.advanceControls
          (profiledRawJointHybridMegaGuardedLinkedLeftPrefixControls A
            strategy hwin controllers initialBank fallbackTag installation
              past input oldOutputOne oldOutputTwo)
          ⟨nextInputOne, nextInputTwo, .right⟩ =
        ((.rightOwner child owner, outputOne),
          (.rightReceiver child receiver, outputTwo)) := by
  simpa only [profiledRawJointHybridMegaGuardedLinkedLeftPrefixControls] using
    (exists_profiledRawJointHybridMegaGuardedLinked_leftPrefix_rightClose_physical
      A strategy hwin controllers initialBank fallbackTag installation past
        input
        (profiledRawJointHybridGuardedLeftPrefixOwner A strategy hwin
          installation (past ++ [input])) oldOutputOne oldOutputTwo
            nextInputOne nextInputTwo)

/-- The guarded-right reversal is already a seed of the generic same-key
recurrent simulation. -/
theorem
    exists_profiledRawJointHybridMegaGuardedLinked_rightPrefix_leftClose_recurrentAt
    (fallbackTag : RetainedTag A strategy hwin)
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (nextInputOne : In₁) (nextInputTwo : In₂) :
    ∃ child, ∃ unitState :
        (FixedOne A strategy hwin controllers initialBank child × Out₁) ×
          (FixedTwo A strategy hwin controllers initialBank child × Out₂),
      ProfiledRawJointIndexedPolicyRecurrentAt A strategy
        (Child A strategy hwin initialBank)
        (profiledRawJointHybridMegaChildSource A strategy hwin initialBank)
        (profiledRawJointHybridMegaChildPolicy A strategy hwin initialBank)
        (profiledRawJointHybridMegaChildControllerBank A strategy hwin
          initialBank)
        Unit Unit
        (GuardedExceptionalOne A strategy hwin controllers initialBank)
        (GuardedExceptionalTwo A strategy hwin controllers initialBank) child
        ((Mega A strategy hwin controllers initialBank fallbackTag
          ).advanceControls
            (profiledRawJointHybridMegaGuardedLinkedRightPrefixControls A
              strategy hwin controllers initialBank fallbackTag installation
                past input oldOutputOne oldOutputTwo)
            ⟨nextInputOne, nextInputTwo, .left⟩)
        unitState := by
  rcases
      exists_profiledRawJointHybridMegaGuardedLinked_rightPrefixControls_leftClose
        A strategy hwin controllers initialBank fallbackTag installation past
          input oldOutputOne oldOutputTwo nextInputOne nextInputTwo with
    ⟨child, outputOne, receiver, outputTwo, owner, hclose⟩
  refine ⟨child,
    (((ProfiledRawJointLeaderFreeOneControl.leftReceiver () receiver),
        outputOne),
      ((ProfiledRawJointLeaderFreeTwoControl.leftOwner () owner),
        outputTwo)), ?_⟩
  rw [hclose]
  exact .matchedLeft receiver owner outputOne outputTwo

/-- The guarded-left reversal is the matched-right recurrent seed. -/
theorem
    exists_profiledRawJointHybridMegaGuardedLinked_leftPrefix_rightClose_recurrentAt
    (fallbackTag : RetainedTag A strategy hwin)
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (past : List (In₁ × In₂)) (input : In₁ × In₂)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (nextInputOne : In₁) (nextInputTwo : In₂) :
    ∃ child, ∃ unitState :
        (FixedOne A strategy hwin controllers initialBank child × Out₁) ×
          (FixedTwo A strategy hwin controllers initialBank child × Out₂),
      ProfiledRawJointIndexedPolicyRecurrentAt A strategy
        (Child A strategy hwin initialBank)
        (profiledRawJointHybridMegaChildSource A strategy hwin initialBank)
        (profiledRawJointHybridMegaChildPolicy A strategy hwin initialBank)
        (profiledRawJointHybridMegaChildControllerBank A strategy hwin
          initialBank)
        Unit Unit
        (GuardedExceptionalOne A strategy hwin controllers initialBank)
        (GuardedExceptionalTwo A strategy hwin controllers initialBank) child
        ((Mega A strategy hwin controllers initialBank fallbackTag
          ).advanceControls
            (profiledRawJointHybridMegaGuardedLinkedLeftPrefixControls A
              strategy hwin controllers initialBank fallbackTag installation
                past input oldOutputOne oldOutputTwo)
            ⟨nextInputOne, nextInputTwo, .right⟩)
        unitState := by
  rcases
      exists_profiledRawJointHybridMegaGuardedLinked_leftPrefixControls_rightClose
        A strategy hwin controllers initialBank fallbackTag installation past
          input oldOutputOne oldOutputTwo nextInputOne nextInputTwo with
    ⟨child, outputOne, owner, outputTwo, receiver, hclose⟩
  refine ⟨child,
    (((ProfiledRawJointLeaderFreeOneControl.rightOwner () owner), outputOne),
      ((ProfiledRawJointLeaderFreeTwoControl.rightReceiver () receiver),
        outputTwo)), ?_⟩
  rw [hclose]
  exact .matchedRight owner receiver outputOne outputTwo

end


end DetParityAutomaton

end DistributedSynthesis
