/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridMegaGuardedLinkedTrajectory
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointUnitFixedTailOperational
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointUnitDummyExceptionalAdapter

/-!
# Fresh fixed-policy handoff of the guarded mega-linked front

A checked guarded strict prefix retains a literal opposite root.  The guarded
close now restarts that root at the canonical `.first` row, independently of
the predecessor receiver row.  Consequently its two physical successor
controls are exactly the first round of the ordinary fresh matched carrier.

This file records that exact recurrent seed and the corresponding fixed-tail
acceptance theorem.  The remaining global argument only has to identify the
checker state before the close with the root's `.first` coordinate.
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

private abbrev Child :=
  ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank

private abbrev GuardedExceptionalOne :=
  ProfiledRawJointHybridMegaGuardedLinkedExceptionalOne A strategy hwin
    controllers initialBank

private abbrev GuardedExceptionalTwo :=
  ProfiledRawJointHybridMegaGuardedLinkedExceptionalTwo A strategy hwin
    controllers initialBank

private abbrev Mega (fallbackTag : RetainedTag A strategy hwin) :=
  MegaGuardedLinkedPhysicalController A strategy hwin controllers initialBank
    fallbackTag

private abbrev UnitAdapter (child : Child A strategy hwin initialBank) :=
  profiledRawJointUnitPolicyDummyExceptionalAdapter A strategy
    (profiledRawJointHybridMegaChildSource A strategy hwin initialBank child)
    (profiledRawJointHybridMegaChildPolicy A strategy hwin initialBank child)
    (profiledRawJointHybridMegaChildControllerBank A strategy hwin initialBank
      child)
    (InitialOne := Unit) (InitialTwo := Unit)
    (ExceptionalOne :=
      GuardedExceptionalOne A strategy hwin controllers initialBank)
    (ExceptionalTwo :=
      GuardedExceptionalTwo A strategy hwin controllers initialBank)

private abbrev UnitKernel (child : Child A strategy hwin initialBank) :=
  profiledRawJointUnitPolicyLeaderFreeKernel A strategy
    (profiledRawJointHybridMegaChildSource A strategy hwin initialBank child)
    (profiledRawJointHybridMegaChildPolicy A strategy hwin initialBank child)
    (profiledRawJointHybridMegaChildControllerBank A strategy hwin initialBank
      child)
    (UnitAdapter A strategy hwin controllers initialBank child)

/-- Prepend one strict-left input to an infinite fixed-left suffix. -/
def profiledRawJointHybridMegaGuardedPrependLeftInput
    (input : In₁ × In₂) (tail : Nat → In₁ × In₂) : Nat → In₁ × In₂
  | 0 => input
  | n + 1 => tail n

/-- Prepend one strict-right input to an infinite fixed-right suffix. -/
def profiledRawJointHybridMegaGuardedPrependRightInput
    (input : In₂ × In₁) (tail : Nat → In₂ × In₁) : Nat → In₂ × In₁
  | 0 => input
  | n + 1 => tail n

/-- A literal left root is accepted from its canonical `.first` checker
coordinate along a close round followed by an arbitrary all-left tail. -/
theorem
    profiledRawJointHybridMegaGuardedFreshMatchedLeft_acceptsFrom_first
    (root : ProfiledRawJointHybridMegaGuardedRightTargetRoot A strategy hwin
      initialBank)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (input : In₁ × In₂) (tail : Nat → In₁ × In₂) :
    let child := root.1
    let source := profiledRawJointHybridMegaChildSource A strategy hwin
      initialBank child
    let policy := profiledRawJointHybridMegaChildPolicy A strategy hwin
      initialBank child
    let bank := profiledRawJointHybridMegaChildControllerBank A strategy hwin
      initialBank child
    let adapter := UnitAdapter A strategy hwin controllers initialBank child
    let unit := UnitKernel A strategy hwin controllers initialBank child
    let fresh := profiledRawJointUnitFreshMatchedLeftState A strategy source
      policy bank adapter root.2 .first oldOutputOne oldOutputTwo
    let inputs := profiledRawJointHybridMegaGuardedPrependLeftInput input tail
    A.AcceptsFrom (pairedCodeStateForRow A .first root.2.slot.1.1)
      ((unit.globalMachine.reroot fresh).globalMachineTraceWord
        unit.globalOutputOne unit.globalOutputTwo
        (profiledRawJointUnitStrictLeftEnvironment inputs)) := by
  dsimp only
  exact profiledRawJointUnitFreshMatchedLeft_acceptsFrom A strategy
    (profiledRawJointHybridMegaChildSource A strategy hwin initialBank root.1)
    (profiledRawJointHybridMegaChildPolicy A strategy hwin initialBank root.1)
    (profiledRawJointHybridMegaChildControllerBank A strategy hwin initialBank
      root.1)
    (UnitAdapter A strategy hwin controllers initialBank root.1) root.2 .first
      oldOutputOne oldOutputTwo
      (profiledRawJointHybridMegaGuardedPrependLeftInput input tail)

/-- Canonical fixed-right mirror. -/
theorem
    profiledRawJointHybridMegaGuardedFreshMatchedRight_acceptsFrom_first
    (root : ProfiledRawJointHybridMegaGuardedLeftTargetRoot A strategy hwin
      initialBank)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (input : In₂ × In₁) (tail : Nat → In₂ × In₁) :
    let child := root.1
    let source := profiledRawJointHybridMegaChildSource A strategy hwin
      initialBank child
    let policy := profiledRawJointHybridMegaChildPolicy A strategy hwin
      initialBank child
    let bank := profiledRawJointHybridMegaChildControllerBank A strategy hwin
      initialBank child
    let adapter := UnitAdapter A strategy hwin controllers initialBank child
    let unit := UnitKernel A strategy hwin controllers initialBank child
    let fresh := profiledRawJointUnitFreshMatchedRightState A strategy source
      policy bank adapter root.2 .first oldOutputOne oldOutputTwo
    let inputs := profiledRawJointHybridMegaGuardedPrependRightInput input tail
    A.AcceptsFrom (pairedCodeStateForRow A .first root.2.slot.1.1)
      ((unit.globalMachine.reroot fresh).globalMachineTraceWord
        unit.globalOutputOne unit.globalOutputTwo
        (profiledRawJointUnitStrictRightEnvironment inputs)) := by
  dsimp only
  exact profiledRawJointUnitFreshMatchedRight_acceptsFrom A strategy
    (profiledRawJointHybridMegaChildSource A strategy hwin initialBank root.1)
    (profiledRawJointHybridMegaChildPolicy A strategy hwin initialBank root.1)
    (profiledRawJointHybridMegaChildControllerBank A strategy hwin initialBank
      root.1)
    (UnitAdapter A strategy hwin controllers initialBank root.1) root.2 .first
      oldOutputOne oldOutputTwo
      (profiledRawJointHybridMegaGuardedPrependRightInput input tail)

/-! ## Exact operational close as the first fresh round -/

/-- The concrete guarded-right reversal and the first round of the fresh
matched-left Unit carrier are related at the literal looked-up child. -/
theorem
    profiledRawJointHybridMegaGuardedLinked_rightPrefix_leftClose_fresh
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
    let child := root.1
    let source := profiledRawJointHybridMegaChildSource A strategy hwin
      initialBank child
    let policy := profiledRawJointHybridMegaChildPolicy A strategy hwin
      initialBank child
    let bank := profiledRawJointHybridMegaChildControllerBank A strategy hwin
      initialBank child
    let adapter := UnitAdapter A strategy hwin controllers initialBank child
    let unit := UnitKernel A strategy hwin controllers initialBank child
    let fresh := profiledRawJointUnitFreshMatchedLeftState A strategy source
      policy bank adapter root.2 .first oldOutputOne oldOutputTwo
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
      (unit.physicalController.advanceControls fresh
        ⟨nextInputOne, nextInputTwo, .left⟩) := by
  dsimp only
  let state :=
    profiledRawJointHybridGuardedRightPrefixReceiverAfter A strategy hwin
      installation past input
  let source := profiledRawJointHybridMegaChildSource A strategy hwin
    initialBank root.1
  let policy := profiledRawJointHybridMegaChildPolicy A strategy hwin
    initialBank root.1
  let bank := profiledRawJointHybridMegaChildControllerBank A strategy hwin
    initialBank root.1
  let restart := profiledRawJointUnitRestartLeft A strategy source policy bank
    root.2 .first
  let nextReceiver := continueProfiledRawJointUnitLeftPolicyReceiver A
    strategy source policy bank restart.2 restart.1
      (nextInputOne, nextInputTwo)
  let nextOwner := stepProfiledRawJointUnitLeftPolicyOwner A strategy source
    policy bank restart.1 nextInputTwo
  let receiver : ProfiledRawJointHybridMegaLeftReceiver A strategy hwin
      initialBank root.1 := nextReceiver.2
  let owner : ProfiledRawJointHybridMegaLeftOwner A strategy hwin initialBank
      root.1 := nextOwner.2
  have hrecv :=
    profiledRawJointHybridMegaGuardedRightCloseReceiverOne?_some A strategy
      hwin initialBank state root hroot nextInputOne nextInputTwo
  have howner :=
    profiledRawJointHybridMegaGuardedRightCloseOwnerTwo?_some A strategy hwin
      initialBank state root hroot nextInputTwo
  have hone :
      (profiledRawJointHybridMegaGuardedLinkedExceptionalAdapter A strategy
        hwin controllers initialBank fallbackTag).otherRecvOne
          (.exceptional (.inr (.inr (.inl
            (profiledRawJointHybridGuardedRightPrefixOwner A strategy hwin
              installation (past ++ [input])))))) nextInputOne
          (.exceptional (.inr (.inr (.inl state)))) nextInputTwo =
        (nextReceiver.1, .leftReceiver root.1 receiver) := by
    change
      (match
        profiledRawJointHybridMegaGuardedRightCloseReceiverOne? A strategy
          hwin initialBank state nextInputOne nextInputTwo with
      | none => _
      | some installed =>
          (installed.1,
            ProfiledRawJointLeaderFreeOneControl.leftReceiver installed.2.1
              installed.2.2)) = _
    rw [hrecv]
  have htwo :
      (profiledRawJointHybridMegaGuardedLinkedExceptionalAdapter A strategy
        hwin controllers initialBank fallbackTag).exceptionalNoRecvTwo
          (.inr (.inr (.inl state))) nextInputTwo =
        (nextOwner.1, .leftOwner root.1 owner) := by
    change
      (match
        profiledRawJointHybridMegaGuardedRightCloseOwnerTwo? A strategy hwin
          initialBank state nextInputTwo with
      | none => _
      | some installed =>
          (installed.1,
            ProfiledRawJointLeaderFreeTwoControl.leftOwner installed.2.1
              installed.2.2)) = _
    rw [howner]
    rfl
  have hindexed :
      (Mega A strategy hwin controllers initialBank fallbackTag).advanceControls
          (profiledRawJointHybridMegaGuardedLinkedRightPrefixControls A
            strategy hwin controllers initialBank fallbackTag installation
              past input oldOutputOne oldOutputTwo)
          ⟨nextInputOne, nextInputTwo, .left⟩ =
        (((.leftReceiver root.1 receiver), nextReceiver.1),
          ((.leftOwner root.1 owner), nextOwner.1)) := by
    apply Prod.ext
    · change
        (((profiledRawJointHybridMegaGuardedLinkedExceptionalAdapter A
          strategy hwin controllers initialBank fallbackTag).otherRecvOne
            (.exceptional (.inr (.inr (.inl
              (profiledRawJointHybridGuardedRightPrefixOwner A strategy hwin
                installation (past ++ [input])))))) nextInputOne
            (.exceptional (.inr (.inr (.inl state)))) nextInputTwo).2,
          ((profiledRawJointHybridMegaGuardedLinkedExceptionalAdapter A
          strategy hwin controllers initialBank fallbackTag).otherRecvOne
            (.exceptional (.inr (.inr (.inl
              (profiledRawJointHybridGuardedRightPrefixOwner A strategy hwin
                installation (past ++ [input])))))) nextInputOne
            (.exceptional (.inr (.inr (.inl state)))) nextInputTwo).1) = _
      rw [hone]
    · change
        (((profiledRawJointHybridMegaGuardedLinkedExceptionalAdapter A
          strategy hwin controllers initialBank fallbackTag
            ).exceptionalNoRecvTwo
              (.inr (.inr (.inl state))) nextInputTwo).2,
          ((profiledRawJointHybridMegaGuardedLinkedExceptionalAdapter A
          strategy hwin controllers initialBank fallbackTag
            ).exceptionalNoRecvTwo
              (.inr (.inr (.inl state))) nextInputTwo).1) = _
      rw [htwo]
  rw [hindexed]
  change ProfiledRawJointIndexedPolicyRecurrentAt A strategy
      (Child A strategy hwin initialBank)
      (profiledRawJointHybridMegaChildSource A strategy hwin initialBank)
      (profiledRawJointHybridMegaChildPolicy A strategy hwin initialBank)
      (profiledRawJointHybridMegaChildControllerBank A strategy hwin
        initialBank) Unit Unit
      (GuardedExceptionalOne A strategy hwin controllers initialBank)
      (GuardedExceptionalTwo A strategy hwin controllers initialBank) root.1
      (((.leftReceiver root.1 receiver), nextReceiver.1),
        ((.leftOwner root.1 owner), nextOwner.1))
      (((.leftReceiver () receiver), nextReceiver.1),
        ((.leftOwner () owner), nextOwner.1))
  exact .matchedLeft receiver owner nextReceiver.1 nextOwner.1

/-- After a first simultaneous round has refreshed the guarded target, a
repeated simultaneous round is the literal `.both` step of the corresponding
fresh matched-left Unit state.  Its successor is the receiver/receiver cross
used by the recurrent simulation. -/
theorem
    profiledRawJointHybridMegaGuardedLinked_rightPrefix_bothClose_fresh
    (fallbackTag : RetainedTag A strategy hwin)
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (leftReceiver :
      ProfiledRawJointHybridGuardedLeftInstalledReceiver A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (nextInputOne : In₁) (nextInputTwo : In₂)
    (root : ProfiledRawJointHybridMegaGuardedRightTargetRoot A strategy hwin
      initialBank)
    (hroot :
      profiledRawJointHybridGuardedRightReceiverTargetRoot? A strategy hwin
          initialBank
          (profiledRawJointHybridGuardedRightPrefixReceiverAfter A strategy
            hwin installation past input) = some root) :
    let child := root.1
    let source := profiledRawJointHybridMegaChildSource A strategy hwin
      initialBank child
    let policy := profiledRawJointHybridMegaChildPolicy A strategy hwin
      initialBank child
    let bank := profiledRawJointHybridMegaChildControllerBank A strategy hwin
      initialBank child
    let adapter := UnitAdapter A strategy hwin controllers initialBank child
    let unit := UnitKernel A strategy hwin controllers initialBank child
    let fresh := profiledRawJointUnitFreshMatchedLeftState A strategy source
      policy bank adapter root.2 .both oldOutputOne oldOutputTwo
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
      (unit.physicalController.advanceControls fresh
        ⟨nextInputOne, nextInputTwo, .both⟩) := by
  dsimp only
  let state :=
    profiledRawJointHybridGuardedRightPrefixReceiverAfter A strategy hwin
      installation past input
  let source := profiledRawJointHybridMegaChildSource A strategy hwin
    initialBank root.1
  let policy := profiledRawJointHybridMegaChildPolicy A strategy hwin
    initialBank root.1
  let bank := profiledRawJointHybridMegaChildControllerBank A strategy hwin
    initialBank root.1
  let restart := profiledRawJointUnitRestartLeft A strategy source policy bank
    root.2 .both
  let nextLeft := continueProfiledRawJointUnitLeftPolicyReceiver A strategy
    source policy bank restart.2 restart.1 (nextInputOne, nextInputTwo)
  let nextRight := profiledRawJointUnitPolicyStartRightReceiver A strategy
    source policy bank restart.2 (nextInputTwo, nextInputOne)
  let left : ProfiledRawJointHybridMegaLeftReceiver A strategy hwin initialBank
      root.1 := nextLeft.2
  let right : ProfiledRawJointHybridMegaRightReceiver A strategy hwin
      initialBank root.1 := nextRight.2
  have hleft :=
    profiledRawJointHybridMegaGuardedRightCloseReceiverOneBoth?_some A strategy
      hwin initialBank state root hroot nextInputOne nextInputTwo
  have hright :=
    profiledRawJointHybridMegaGuardedRightCloseReceiverTwoBoth?_some A strategy
      hwin initialBank state root hroot nextInputTwo nextInputOne
  have hone :
      (profiledRawJointHybridMegaGuardedLinkedExceptionalAdapter A strategy
        hwin controllers initialBank fallbackTag).otherRecvOne
          (.exceptional (.inr (.inr (.inr leftReceiver)))) nextInputOne
          (.exceptional (.inr (.inr (.inl state)))) nextInputTwo =
        (nextLeft.1, .leftReceiver root.1 left) := by
    change
      (match
        profiledRawJointHybridMegaGuardedRightCloseReceiverOneBoth? A strategy
          hwin initialBank state nextInputOne nextInputTwo with
      | none => _
      | some installed =>
          (installed.1,
            ProfiledRawJointLeaderFreeOneControl.leftReceiver installed.2.1
              installed.2.2)) = _
    rw [hleft]
  have htwo :
      (profiledRawJointHybridMegaGuardedLinkedExceptionalAdapter A strategy
        hwin controllers initialBank fallbackTag).otherRecvTwo
          (.exceptional (.inr (.inr (.inl state)))) nextInputTwo
          (.exceptional (.inr (.inr (.inr leftReceiver)))) nextInputOne =
        (nextRight.1, .rightReceiver root.1 right) := by
    change
      (match
        profiledRawJointHybridMegaGuardedRightCloseReceiverTwoBoth? A strategy
          hwin initialBank state nextInputTwo nextInputOne with
      | none => _
      | some installed =>
          (installed.1,
            ProfiledRawJointLeaderFreeTwoControl.rightReceiver installed.2.1
              installed.2.2)) = _
    rw [hright]
  have hindexed :
      (Mega A strategy hwin controllers initialBank fallbackTag).advanceControls
          ((.exceptional (.inr (.inr (.inr leftReceiver))), oldOutputOne),
            (.exceptional (.inr (.inr (.inl state))), oldOutputTwo))
          ⟨nextInputOne, nextInputTwo, .both⟩ =
        (((.leftReceiver root.1 left), nextLeft.1),
          ((.rightReceiver root.1 right), nextRight.1)) := by
    apply Prod.ext
    · change
        (((profiledRawJointHybridMegaGuardedLinkedExceptionalAdapter A
          strategy hwin controllers initialBank fallbackTag).otherRecvOne
            (.exceptional (.inr (.inr (.inr leftReceiver)))) nextInputOne
            (.exceptional (.inr (.inr (.inl state)))) nextInputTwo).2,
          ((profiledRawJointHybridMegaGuardedLinkedExceptionalAdapter A
          strategy hwin controllers initialBank fallbackTag).otherRecvOne
            (.exceptional (.inr (.inr (.inr leftReceiver)))) nextInputOne
            (.exceptional (.inr (.inr (.inl state)))) nextInputTwo).1) = _
      rw [hone]
    · change
        (((profiledRawJointHybridMegaGuardedLinkedExceptionalAdapter A
          strategy hwin controllers initialBank fallbackTag).otherRecvTwo
            (.exceptional (.inr (.inr (.inl state)))) nextInputTwo
            (.exceptional (.inr (.inr (.inr leftReceiver)))) nextInputOne).2,
          ((profiledRawJointHybridMegaGuardedLinkedExceptionalAdapter A
          strategy hwin controllers initialBank fallbackTag).otherRecvTwo
            (.exceptional (.inr (.inr (.inl state)))) nextInputTwo
            (.exceptional (.inr (.inr (.inr leftReceiver)))) nextInputOne).1) = _
      rw [htwo]
  rw [hindexed]
  change ProfiledRawJointIndexedPolicyRecurrentAt A strategy
      (Child A strategy hwin initialBank)
      (profiledRawJointHybridMegaChildSource A strategy hwin initialBank)
      (profiledRawJointHybridMegaChildPolicy A strategy hwin initialBank)
      (profiledRawJointHybridMegaChildControllerBank A strategy hwin
        initialBank) Unit Unit
      (GuardedExceptionalOne A strategy hwin controllers initialBank)
      (GuardedExceptionalTwo A strategy hwin controllers initialBank) root.1
      (((.leftReceiver root.1 left), nextLeft.1),
        ((.rightReceiver root.1 right), nextRight.1))
      (((.leftReceiver () left), nextLeft.1),
        ((.rightReceiver () right), nextRight.1))
  exact .cross left right nextLeft.1 nextRight.1

/-! ## Whole-word splices at the guarded close -/

/-- The repeated-simultaneous handoff also splices the complete physical word:
after its first `.both` round the indexed and fixed-policy runs stay in the
same-key recurrent relation for an arbitrary environment tail. -/
theorem
    profiledRawJointHybridMegaGuardedLinked_rightPrefix_bothClose_traceWord_eq_fresh
    (fallbackTag : RetainedTag A strategy hwin)
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (leftReceiver :
      ProfiledRawJointHybridGuardedLeftInstalledReceiver A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (nextInputOne : In₁) (nextInputTwo : In₂)
    (tail : EnvironmentSequence In₁ In₂)
    (root : ProfiledRawJointHybridMegaGuardedRightTargetRoot A strategy hwin
      initialBank)
    (hroot :
      profiledRawJointHybridGuardedRightReceiverTargetRoot? A strategy hwin
          initialBank
          (profiledRawJointHybridGuardedRightPrefixReceiverAfter A strategy
            hwin installation past input) = some root) :
    let child := root.1
    let source := profiledRawJointHybridMegaChildSource A strategy hwin
      initialBank child
    let policy := profiledRawJointHybridMegaChildPolicy A strategy hwin
      initialBank child
    let bank := profiledRawJointHybridMegaChildControllerBank A strategy hwin
      initialBank child
    let adapter := UnitAdapter A strategy hwin controllers initialBank child
    let unit := UnitKernel A strategy hwin controllers initialBank child
    let fresh := profiledRawJointUnitFreshMatchedLeftState A strategy source
      policy bank adapter root.2 .both oldOutputOne oldOutputTwo
    let env : EnvironmentSequence In₁ In₂ := OmegaWord.prependList
      [⟨nextInputOne, nextInputTwo, .both⟩] tail
    ((Mega A strategy hwin controllers initialBank fallbackTag).globalMachine
        |>.reroot
          ((.exceptional (.inr (.inr (.inr leftReceiver))), oldOutputOne),
            (.exceptional (.inr (.inr (.inl
              (profiledRawJointHybridGuardedRightPrefixReceiverAfter A
                strategy hwin installation past input)))), oldOutputTwo)
          )).globalMachineTraceWord
        (Mega A strategy hwin controllers initialBank fallbackTag
          ).globalOutputOne
        (Mega A strategy hwin controllers initialBank fallbackTag
          ).globalOutputTwo env =
      (unit.globalMachine.reroot fresh).globalMachineTraceWord
        unit.globalOutputOne unit.globalOutputTwo env := by
  classical
  dsimp only
  let env : EnvironmentSequence In₁ In₂ := OmegaWord.prependList
    [⟨nextInputOne, nextInputTwo, .both⟩] tail
  apply profiledRawJointIndexedPolicyRecurrentAt_traceWord_eq_of_advance
    A strategy (Child A strategy hwin initialBank)
      (profiledRawJointHybridMegaChildSource A strategy hwin initialBank)
      (profiledRawJointHybridMegaChildPolicy A strategy hwin initialBank)
      (profiledRawJointHybridMegaChildControllerBank A strategy hwin
        initialBank)
      (profiledRawJointHybridMegaGuardedLinkedExceptionalAdapter A strategy
        hwin controllers initialBank fallbackTag) root.1
      (UnitAdapter A strategy hwin controllers initialBank root.1)
      (((.exceptional (.inr (.inr (.inr leftReceiver)))), oldOutputOne),
        ((.exceptional (.inr (.inr (.inl
          (profiledRawJointHybridGuardedRightPrefixReceiverAfter A strategy
            hwin installation past input))))), oldOutputTwo))
      (profiledRawJointUnitFreshMatchedLeftState A strategy
        (profiledRawJointHybridMegaChildSource A strategy hwin initialBank
          root.1)
        (profiledRawJointHybridMegaChildPolicy A strategy hwin initialBank
          root.1)
        (profiledRawJointHybridMegaChildControllerBank A strategy hwin
          initialBank root.1)
        (UnitAdapter A strategy hwin controllers initialBank root.1) root.2
          .both oldOutputOne oldOutputTwo) env
  simpa only [env, OmegaWord.prependList_cons_zero] using
    (profiledRawJointHybridMegaGuardedLinked_rightPrefix_bothClose_fresh A
      strategy hwin controllers initialBank fallbackTag installation past
        input leftReceiver oldOutputOne oldOutputTwo nextInputOne nextInputTwo
          root hroot)

/-- After consuming the repeated-simultaneous handoff round, acceptance from
the refreshed target's `.both` coordinate is exactly acceptance of the fresh
fixed-policy tail.  This word-equality theorem does not itself prove the
first-simultaneous-round checker/target refresh invariant. -/
theorem
    profiledRawJointHybridMegaGuardedLinked_rightPrefix_bothClose_acceptsFrom_both_iff_fresh_tail
    (fallbackTag : RetainedTag A strategy hwin)
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (leftReceiver :
      ProfiledRawJointHybridGuardedLeftInstalledReceiver A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (nextInputOne : In₁) (nextInputTwo : In₂)
    (tail : EnvironmentSequence In₁ In₂)
    (root : ProfiledRawJointHybridMegaGuardedRightTargetRoot A strategy hwin
      initialBank)
    (hroot :
      profiledRawJointHybridGuardedRightReceiverTargetRoot? A strategy hwin
          initialBank
          (profiledRawJointHybridGuardedRightPrefixReceiverAfter A strategy
            hwin installation past input) = some root) :
    let child := root.1
    let source := profiledRawJointHybridMegaChildSource A strategy hwin
      initialBank child
    let policy := profiledRawJointHybridMegaChildPolicy A strategy hwin
      initialBank child
    let bank := profiledRawJointHybridMegaChildControllerBank A strategy hwin
      initialBank child
    let adapter := UnitAdapter A strategy hwin controllers initialBank child
    let unit := UnitKernel A strategy hwin controllers initialBank child
    let fresh := profiledRawJointUnitFreshMatchedLeftState A strategy source
      policy bank adapter root.2 .both oldOutputOne oldOutputTwo
    let env : EnvironmentSequence In₁ In₂ := OmegaWord.prependList
      [⟨nextInputOne, nextInputTwo, .both⟩] tail
    let megaWord :=
      ((Mega A strategy hwin controllers initialBank fallbackTag).globalMachine
          |>.reroot
            ((.exceptional (.inr (.inr (.inr leftReceiver))), oldOutputOne),
              (.exceptional (.inr (.inr (.inl
                (profiledRawJointHybridGuardedRightPrefixReceiverAfter A
                  strategy hwin installation past input)))), oldOutputTwo)
            )).globalMachineTraceWord
          (Mega A strategy hwin controllers initialBank fallbackTag
            ).globalOutputOne
          (Mega A strategy hwin controllers initialBank fallbackTag
            ).globalOutputTwo env
    let freshWord :=
      (unit.globalMachine.reroot fresh).globalMachineTraceWord
        unit.globalOutputOne unit.globalOutputTwo env
    A.AcceptsFrom (pairedCodeStateForRow A .both root.2.slot.1.1)
        (OmegaWord.drop megaWord 1) ↔
      A.AcceptsFrom (pairedCodeStateForRow A .both root.2.slot.1.1)
        (OmegaWord.drop freshWord 1) := by
  dsimp only
  rw [profiledRawJointHybridMegaGuardedLinked_rightPrefix_bothClose_traceWord_eq_fresh
    A strategy hwin controllers initialBank fallbackTag installation past
      input leftReceiver oldOutputOne oldOutputTwo nextInputOne nextInputTwo
        tail root hroot]

/-- A guarded-right reversal followed by an all-left suffix emits exactly the
fresh fixed-policy word rooted at the checked target. -/
theorem
    profiledRawJointHybridMegaGuardedLinked_rightPrefix_leftClose_traceWord_eq_fresh
    (fallbackTag : RetainedTag A strategy hwin)
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (nextInputOne : In₁) (nextInputTwo : In₂)
    (tail : Nat → In₁ × In₂)
    (root : ProfiledRawJointHybridMegaGuardedRightTargetRoot A strategy hwin
      initialBank)
    (hroot :
      profiledRawJointHybridGuardedRightReceiverTargetRoot? A strategy hwin
          initialBank
          (profiledRawJointHybridGuardedRightPrefixReceiverAfter A strategy
            hwin installation past input) = some root) :
    let child := root.1
    let source := profiledRawJointHybridMegaChildSource A strategy hwin
      initialBank child
    let policy := profiledRawJointHybridMegaChildPolicy A strategy hwin
      initialBank child
    let bank := profiledRawJointHybridMegaChildControllerBank A strategy hwin
      initialBank child
    let adapter := UnitAdapter A strategy hwin controllers initialBank child
    let unit := UnitKernel A strategy hwin controllers initialBank child
    let fresh := profiledRawJointUnitFreshMatchedLeftState A strategy source
      policy bank adapter root.2 .first oldOutputOne oldOutputTwo
    let env := profiledRawJointUnitStrictLeftEnvironment
      (profiledRawJointHybridMegaGuardedPrependLeftInput
        (nextInputOne, nextInputTwo) tail)
    ((Mega A strategy hwin controllers initialBank fallbackTag).globalMachine
        |>.reroot
          (profiledRawJointHybridMegaGuardedLinkedRightPrefixControls A
            strategy hwin controllers initialBank fallbackTag installation
              past input oldOutputOne oldOutputTwo)).globalMachineTraceWord
        (Mega A strategy hwin controllers initialBank fallbackTag
          ).globalOutputOne
        (Mega A strategy hwin controllers initialBank fallbackTag
          ).globalOutputTwo env =
      (unit.globalMachine.reroot fresh).globalMachineTraceWord
        unit.globalOutputOne unit.globalOutputTwo env := by
  classical
  dsimp only
  let env := profiledRawJointUnitStrictLeftEnvironment
    (profiledRawJointHybridMegaGuardedPrependLeftInput
      (nextInputOne, nextInputTwo) tail)
  apply profiledRawJointIndexedPolicyRecurrentAt_traceWord_eq_of_advance
    A strategy (Child A strategy hwin initialBank)
      (profiledRawJointHybridMegaChildSource A strategy hwin initialBank)
      (profiledRawJointHybridMegaChildPolicy A strategy hwin initialBank)
      (profiledRawJointHybridMegaChildControllerBank A strategy hwin
        initialBank)
      (profiledRawJointHybridMegaGuardedLinkedExceptionalAdapter A strategy
        hwin controllers initialBank fallbackTag) root.1
      (UnitAdapter A strategy hwin controllers initialBank root.1)
      (profiledRawJointHybridMegaGuardedLinkedRightPrefixControls A strategy
        hwin controllers initialBank fallbackTag installation past input
          oldOutputOne oldOutputTwo)
      (profiledRawJointUnitFreshMatchedLeftState A strategy
        (profiledRawJointHybridMegaChildSource A strategy hwin initialBank
          root.1)
        (profiledRawJointHybridMegaChildPolicy A strategy hwin initialBank
          root.1)
        (profiledRawJointHybridMegaChildControllerBank A strategy hwin
          initialBank root.1)
        (UnitAdapter A strategy hwin controllers initialBank root.1) root.2
          .first oldOutputOne oldOutputTwo) env
  simpa [env, profiledRawJointHybridMegaGuardedPrependLeftInput,
    profiledRawJointUnitStrictLeftEnvironment] using
    (profiledRawJointHybridMegaGuardedLinked_rightPrefix_leftClose_fresh A
      strategy hwin controllers initialBank fallbackTag installation past
        input oldOutputOne oldOutputTwo nextInputOne nextInputTwo root hroot)

/-- Consequently the complete guarded close plus fixed-left tail is accepted
from the target's exact `.first` checker coordinate. -/
theorem
    profiledRawJointHybridMegaGuardedLinked_rightPrefix_leftClose_acceptsFrom_first
    (fallbackTag : RetainedTag A strategy hwin)
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (nextInputOne : In₁) (nextInputTwo : In₂)
    (tail : Nat → In₁ × In₂)
    (root : ProfiledRawJointHybridMegaGuardedRightTargetRoot A strategy hwin
      initialBank)
    (hroot :
      profiledRawJointHybridGuardedRightReceiverTargetRoot? A strategy hwin
          initialBank
          (profiledRawJointHybridGuardedRightPrefixReceiverAfter A strategy
            hwin installation past input) = some root) :
    let mega := Mega A strategy hwin controllers initialBank fallbackTag
    let env := profiledRawJointUnitStrictLeftEnvironment
      (profiledRawJointHybridMegaGuardedPrependLeftInput
        (nextInputOne, nextInputTwo) tail)
    A.AcceptsFrom (pairedCodeStateForRow A .first root.2.slot.1.1)
      ((mega.globalMachine.reroot
          (profiledRawJointHybridMegaGuardedLinkedRightPrefixControls A
            strategy hwin controllers initialBank fallbackTag installation
              past input oldOutputOne oldOutputTwo)).globalMachineTraceWord
        mega.globalOutputOne mega.globalOutputTwo env) := by
  dsimp only
  rw [profiledRawJointHybridMegaGuardedLinked_rightPrefix_leftClose_traceWord_eq_fresh
    A strategy hwin controllers initialBank fallbackTag installation past input
      oldOutputOne oldOutputTwo nextInputOne nextInputTwo tail root hroot]
  exact
    profiledRawJointHybridMegaGuardedFreshMatchedLeft_acceptsFrom_first A
      strategy hwin controllers initialBank root oldOutputOne oldOutputTwo
        (nextInputOne, nextInputTwo) tail

/-- Guarded-left / fresh matched-right mirror. -/
theorem
    profiledRawJointHybridMegaGuardedLinked_leftPrefix_rightClose_fresh
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
    let child := root.1
    let source := profiledRawJointHybridMegaChildSource A strategy hwin
      initialBank child
    let policy := profiledRawJointHybridMegaChildPolicy A strategy hwin
      initialBank child
    let bank := profiledRawJointHybridMegaChildControllerBank A strategy hwin
      initialBank child
    let adapter := UnitAdapter A strategy hwin controllers initialBank child
    let unit := UnitKernel A strategy hwin controllers initialBank child
    let fresh := profiledRawJointUnitFreshMatchedRightState A strategy source
      policy bank adapter root.2 .first oldOutputOne oldOutputTwo
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
      (unit.physicalController.advanceControls fresh
        ⟨nextInputOne, nextInputTwo, .right⟩) := by
  dsimp only
  let state :=
    profiledRawJointHybridGuardedLeftPrefixReceiverAfter A strategy hwin
      installation past input
  let source := profiledRawJointHybridMegaChildSource A strategy hwin
    initialBank root.1
  let policy := profiledRawJointHybridMegaChildPolicy A strategy hwin
    initialBank root.1
  let bank := profiledRawJointHybridMegaChildControllerBank A strategy hwin
    initialBank root.1
  let restart := profiledRawJointUnitRestartRight A strategy source policy bank
    root.2 .first
  let nextOwner := stepProfiledRawJointUnitRightPolicyOwner A strategy source
    policy bank restart.1 nextInputOne
  let nextReceiver := continueProfiledRawJointUnitRightPolicyReceiver A
    strategy source policy bank restart.2 restart.1
      (nextInputTwo, nextInputOne)
  let owner : ProfiledRawJointHybridMegaRightOwner A strategy hwin initialBank
      root.1 := nextOwner.2
  let receiver : ProfiledRawJointHybridMegaRightReceiver A strategy hwin
      initialBank root.1 := nextReceiver.2
  have howner :=
    profiledRawJointHybridMegaGuardedLeftCloseOwnerOne?_some A strategy hwin
      initialBank state root hroot nextInputOne
  have hrecv :=
    profiledRawJointHybridMegaGuardedLeftCloseReceiverTwo?_some A strategy
      hwin initialBank state root hroot nextInputTwo nextInputOne
  have hone :
      (profiledRawJointHybridMegaGuardedLinkedExceptionalAdapter A strategy
        hwin controllers initialBank fallbackTag).exceptionalNoRecvOne
          (.inr (.inr (.inr state))) nextInputOne =
        (nextOwner.1, .rightOwner root.1 owner) := by
    change
      (match
        profiledRawJointHybridMegaGuardedLeftCloseOwnerOne? A strategy hwin
          initialBank state nextInputOne with
      | none => _
      | some installed =>
          (installed.1,
            ProfiledRawJointLeaderFreeOneControl.rightOwner installed.2.1
              installed.2.2)) = _
    rw [howner]
    rfl
  have htwo :
      (profiledRawJointHybridMegaGuardedLinkedExceptionalAdapter A strategy
        hwin controllers initialBank fallbackTag).otherRecvTwo
          (.exceptional (.inr (.inr (.inr
            (profiledRawJointHybridGuardedLeftPrefixOwner A strategy hwin
              installation (past ++ [input])))))) nextInputTwo
          (.exceptional (.inr (.inr (.inr state)))) nextInputOne =
        (nextReceiver.1, .rightReceiver root.1 receiver) := by
    change
      (match
        profiledRawJointHybridMegaGuardedLeftCloseReceiverTwo? A strategy
          hwin initialBank state nextInputTwo nextInputOne with
      | none => _
      | some installed =>
          (installed.1,
            ProfiledRawJointLeaderFreeTwoControl.rightReceiver installed.2.1
              installed.2.2)) = _
    rw [hrecv]
  have hindexed :
      (Mega A strategy hwin controllers initialBank fallbackTag).advanceControls
          (profiledRawJointHybridMegaGuardedLinkedLeftPrefixControls A strategy
            hwin controllers initialBank fallbackTag installation past input
              oldOutputOne oldOutputTwo)
          ⟨nextInputOne, nextInputTwo, .right⟩ =
        (((.rightOwner root.1 owner), nextOwner.1),
          ((.rightReceiver root.1 receiver), nextReceiver.1)) := by
    apply Prod.ext
    · change
        (((profiledRawJointHybridMegaGuardedLinkedExceptionalAdapter A
          strategy hwin controllers initialBank fallbackTag
            ).exceptionalNoRecvOne
              (.inr (.inr (.inr state))) nextInputOne).2,
          ((profiledRawJointHybridMegaGuardedLinkedExceptionalAdapter A
          strategy hwin controllers initialBank fallbackTag
            ).exceptionalNoRecvOne
              (.inr (.inr (.inr state))) nextInputOne).1) = _
      rw [hone]
    · change
        (((profiledRawJointHybridMegaGuardedLinkedExceptionalAdapter A
          strategy hwin controllers initialBank fallbackTag).otherRecvTwo
            (.exceptional (.inr (.inr (.inr
              (profiledRawJointHybridGuardedLeftPrefixOwner A strategy hwin
                installation (past ++ [input])))))) nextInputTwo
            (.exceptional (.inr (.inr (.inr state)))) nextInputOne).2,
          ((profiledRawJointHybridMegaGuardedLinkedExceptionalAdapter A
          strategy hwin controllers initialBank fallbackTag).otherRecvTwo
            (.exceptional (.inr (.inr (.inr
              (profiledRawJointHybridGuardedLeftPrefixOwner A strategy hwin
                installation (past ++ [input])))))) nextInputTwo
            (.exceptional (.inr (.inr (.inr state)))) nextInputOne).1) = _
      rw [htwo]
  rw [hindexed]
  change ProfiledRawJointIndexedPolicyRecurrentAt A strategy
      (Child A strategy hwin initialBank)
      (profiledRawJointHybridMegaChildSource A strategy hwin initialBank)
      (profiledRawJointHybridMegaChildPolicy A strategy hwin initialBank)
      (profiledRawJointHybridMegaChildControllerBank A strategy hwin
        initialBank) Unit Unit
      (GuardedExceptionalOne A strategy hwin controllers initialBank)
      (GuardedExceptionalTwo A strategy hwin controllers initialBank) root.1
      (((.rightOwner root.1 owner), nextOwner.1),
        ((.rightReceiver root.1 receiver), nextReceiver.1))
      (((.rightOwner () owner), nextOwner.1),
        ((.rightReceiver () receiver), nextReceiver.1))
  exact .matchedRight owner receiver nextOwner.1 nextReceiver.1

/-- Guarded-left / fixed-right whole-word splice. -/
theorem
    profiledRawJointHybridMegaGuardedLinked_leftPrefix_rightClose_traceWord_eq_fresh
    (fallbackTag : RetainedTag A strategy hwin)
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (past : List (In₁ × In₂)) (input : In₁ × In₂)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (nextInputOne : In₁) (nextInputTwo : In₂)
    (tail : Nat → In₂ × In₁)
    (root : ProfiledRawJointHybridMegaGuardedLeftTargetRoot A strategy hwin
      initialBank)
    (hroot :
      profiledRawJointHybridGuardedLeftReceiverTargetRoot? A strategy hwin
          initialBank
          (profiledRawJointHybridGuardedLeftPrefixReceiverAfter A strategy
            hwin installation past input) = some root) :
    let child := root.1
    let source := profiledRawJointHybridMegaChildSource A strategy hwin
      initialBank child
    let policy := profiledRawJointHybridMegaChildPolicy A strategy hwin
      initialBank child
    let bank := profiledRawJointHybridMegaChildControllerBank A strategy hwin
      initialBank child
    let adapter := UnitAdapter A strategy hwin controllers initialBank child
    let unit := UnitKernel A strategy hwin controllers initialBank child
    let fresh := profiledRawJointUnitFreshMatchedRightState A strategy source
      policy bank adapter root.2 .first oldOutputOne oldOutputTwo
    let env := profiledRawJointUnitStrictRightEnvironment
      (profiledRawJointHybridMegaGuardedPrependRightInput
        (nextInputTwo, nextInputOne) tail)
    ((Mega A strategy hwin controllers initialBank fallbackTag).globalMachine
        |>.reroot
          (profiledRawJointHybridMegaGuardedLinkedLeftPrefixControls A
            strategy hwin controllers initialBank fallbackTag installation
              past input oldOutputOne oldOutputTwo)).globalMachineTraceWord
        (Mega A strategy hwin controllers initialBank fallbackTag
          ).globalOutputOne
        (Mega A strategy hwin controllers initialBank fallbackTag
          ).globalOutputTwo env =
      (unit.globalMachine.reroot fresh).globalMachineTraceWord
        unit.globalOutputOne unit.globalOutputTwo env := by
  classical
  dsimp only
  let env := profiledRawJointUnitStrictRightEnvironment
    (profiledRawJointHybridMegaGuardedPrependRightInput
      (nextInputTwo, nextInputOne) tail)
  apply profiledRawJointIndexedPolicyRecurrentAt_traceWord_eq_of_advance
    A strategy (Child A strategy hwin initialBank)
      (profiledRawJointHybridMegaChildSource A strategy hwin initialBank)
      (profiledRawJointHybridMegaChildPolicy A strategy hwin initialBank)
      (profiledRawJointHybridMegaChildControllerBank A strategy hwin
        initialBank)
      (profiledRawJointHybridMegaGuardedLinkedExceptionalAdapter A strategy
        hwin controllers initialBank fallbackTag) root.1
      (UnitAdapter A strategy hwin controllers initialBank root.1)
      (profiledRawJointHybridMegaGuardedLinkedLeftPrefixControls A strategy
        hwin controllers initialBank fallbackTag installation past input
          oldOutputOne oldOutputTwo)
      (profiledRawJointUnitFreshMatchedRightState A strategy
        (profiledRawJointHybridMegaChildSource A strategy hwin initialBank
          root.1)
        (profiledRawJointHybridMegaChildPolicy A strategy hwin initialBank
          root.1)
        (profiledRawJointHybridMegaChildControllerBank A strategy hwin
          initialBank root.1)
        (UnitAdapter A strategy hwin controllers initialBank root.1) root.2
          .first oldOutputOne oldOutputTwo) env
  simpa [env, profiledRawJointHybridMegaGuardedPrependRightInput,
    profiledRawJointUnitStrictRightEnvironment] using
    (profiledRawJointHybridMegaGuardedLinked_leftPrefix_rightClose_fresh A
      strategy hwin controllers initialBank fallbackTag installation past
        input oldOutputOne oldOutputTwo nextInputOne nextInputTwo root hroot)

/-- The mirror guarded close plus fixed-right tail is accepted from the exact
checked `.first` coordinate. -/
theorem
    profiledRawJointHybridMegaGuardedLinked_leftPrefix_rightClose_acceptsFrom_first
    (fallbackTag : RetainedTag A strategy hwin)
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (past : List (In₁ × In₂)) (input : In₁ × In₂)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (nextInputOne : In₁) (nextInputTwo : In₂)
    (tail : Nat → In₂ × In₁)
    (root : ProfiledRawJointHybridMegaGuardedLeftTargetRoot A strategy hwin
      initialBank)
    (hroot :
      profiledRawJointHybridGuardedLeftReceiverTargetRoot? A strategy hwin
          initialBank
          (profiledRawJointHybridGuardedLeftPrefixReceiverAfter A strategy
            hwin installation past input) = some root) :
    let mega := Mega A strategy hwin controllers initialBank fallbackTag
    let env := profiledRawJointUnitStrictRightEnvironment
      (profiledRawJointHybridMegaGuardedPrependRightInput
        (nextInputTwo, nextInputOne) tail)
    A.AcceptsFrom (pairedCodeStateForRow A .first root.2.slot.1.1)
      ((mega.globalMachine.reroot
          (profiledRawJointHybridMegaGuardedLinkedLeftPrefixControls A
            strategy hwin controllers initialBank fallbackTag installation
              past input oldOutputOne oldOutputTwo)).globalMachineTraceWord
        mega.globalOutputOne mega.globalOutputTwo env) := by
  dsimp only
  rw [profiledRawJointHybridMegaGuardedLinked_leftPrefix_rightClose_traceWord_eq_fresh
    A strategy hwin controllers initialBank fallbackTag installation past input
      oldOutputOne oldOutputTwo nextInputOne nextInputTwo tail root hroot]
  exact
    profiledRawJointHybridMegaGuardedFreshMatchedRight_acceptsFrom_first A
      strategy hwin controllers initialBank root oldOutputOne oldOutputTwo
        (nextInputTwo, nextInputOne) tail

end

end DetParityAutomaton

end DistributedSynthesis
