/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridMegaGuardedLinkedFreshHandoff
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointAlignedCanonicalPhysicalSchedule
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridMegaGuardedTargetReachability

/-!
# Checker alignment at a guarded mega close

The guarded receiver stores a checked finite target.  A successful mega-root
lookup stages the target's literal active slot, while the checked-close law
identifies that target with the actual physical scan successor.  Combining
the two facts proves that the canonical `.first` state used by the repaired
fresh restart is exactly the current DPA state after the strict prefix.
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

/-- The `.first` coordinate of the left root selected after a guarded-right
prefix is the literal strict-right scan successor. -/
theorem
    profiledRawJointHybridMegaGuardedRightPrefixTargetRoot_first_eq_scanCurrent
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (root : ProfiledRawJointHybridMegaGuardedRightTargetRoot A strategy hwin
      initialBank)
    (hroot :
      profiledRawJointHybridGuardedRightReceiverTargetRoot? A strategy hwin
          initialBank
          (profiledRawJointHybridGuardedRightPrefixReceiverAfter A strategy
            hwin installation past input) = some root) :
    let pair := profiledRawJointHybridGuardedCommonPairAt A strategy hwin
      installation
    let state := profiledRawJointGuardedCommonRightFiniteStateAfter A strategy
      hwin pair past
    let monitor := profiledRawJointGuardedRightPhysicalSiblingMonitor A
      pair.1.1.1 false
    let controller := (pair.1.1).memberController A false
    let record := narrowedRecord monitor (controller.labelOf state.1) state.2
      input
    pairedCodeStateForRow A .first root.2.slot.1.1 =
      (pairedRightScanPairForRow A .both
        (pairedRightScanStep A state.2.base.2.1
          (profiledRawJointTargetRightPhysicalLetter A record))).1 := by
  dsimp only
  let pair := profiledRawJointHybridGuardedCommonPairAt A strategy hwin
    installation
  let state := profiledRawJointGuardedCommonRightFiniteStateAfter A strategy
    hwin pair past
  let monitor := profiledRawJointGuardedRightPhysicalSiblingMonitor A
    pair.1.1.1 false
  let controller := (pair.1.1).memberController A false
  let record := narrowedRecord monitor (controller.labelOf state.1) state.2
    input
  let target :=
    (profiledRawJointGuardedCommonRightPrefixOutput A strategy hwin pair past
      input).target .both
  have htarget :=
    profiledRawJointHybridGuardedRightPrefixReceiverAfter_target A strategy
      hwin installation past input
  have hrootTarget := hroot
  rw [profiledRawJointHybridGuardedRightReceiverTargetRoot?_some A strategy
      hwin initialBank _ target htarget,
    profiledRawJointHybridGuardedRightPrefixReceiverAfter_installation]
      at hrootTarget
  have hslot :=
    profiledRawJointHybridMegaGuardedRightTargetRoot?_slot A strategy hwin
      initialBank installation target root hrootTarget
  have hprojection :
      profiledRawJointUnitRightTargetProjection A target =
        .inr (.inr root.2.slot) := by
    simp [profiledRawJointUnitRightTargetProjection, hslot]
  have hclose :=
    profiledRawJointHybridGuardedRightPrefixTargetCloses A strategy hwin
      installation past input .both
  change erasePairedProfiledState A
      (profiledRawJointUnitRightTargetProjection A target) =
    pairedRightCloseTarget A state.2.base.2.1 .both
      (profiledRawJointTargetRightPhysicalLetter A record) at hclose
  rw [hprojection] at hclose
  exact
    pairedCodeStateForRow_first_eq_rightScanStep_selected_current_of_exactTarget
      A root.2.slot state.2.base.2.1 .both
        (profiledRawJointTargetRightPhysicalLetter A record) hclose

/-- The `.both` coordinate of the same selected root is the counterfactual
simultaneous successor of the same final strict-prefix occurrence.  The
receiver/receiver branch uses this coordinate structurally, but this theorem
does not identify it with the checker state after a later simultaneous round. -/
theorem
    profiledRawJointHybridMegaGuardedRightPrefixTargetRoot_both_eq_scanCurrent
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (root : ProfiledRawJointHybridMegaGuardedRightTargetRoot A strategy hwin
      initialBank)
    (hroot :
      profiledRawJointHybridGuardedRightReceiverTargetRoot? A strategy hwin
          initialBank
          (profiledRawJointHybridGuardedRightPrefixReceiverAfter A strategy
            hwin installation past input) = some root) :
    let pair := profiledRawJointHybridGuardedCommonPairAt A strategy hwin
      installation
    let state := profiledRawJointGuardedCommonRightFiniteStateAfter A strategy
      hwin pair past
    let monitor := profiledRawJointGuardedRightPhysicalSiblingMonitor A
      pair.1.1.1 false
    let controller := (pair.1.1).memberController A false
    let record := narrowedRecord monitor (controller.labelOf state.1) state.2
      input
    pairedCodeStateForRow A .both root.2.slot.1.1 =
      A.step (pairedRightScanPairForRow A .both state.2.base.2.1).1
        (bothRoundRecord
          ((profiledRawJointTargetRightPhysicalLetter A record).1.2,
            (profiledRawJointTargetRightPhysicalLetter A record).1.1)
          (pairedRightClosingForRow .both
            (profiledRawJointTargetRightPhysicalLetter A record).2.1)
          (pairedRightInformedForRow .both
            (profiledRawJointTargetRightPhysicalLetter A record).2.1)) := by
  dsimp only
  let pair := profiledRawJointHybridGuardedCommonPairAt A strategy hwin
    installation
  let state := profiledRawJointGuardedCommonRightFiniteStateAfter A strategy
    hwin pair past
  let monitor := profiledRawJointGuardedRightPhysicalSiblingMonitor A
    pair.1.1.1 false
  let controller := (pair.1.1).memberController A false
  let record := narrowedRecord monitor (controller.labelOf state.1) state.2
    input
  let target :=
    (profiledRawJointGuardedCommonRightPrefixOutput A strategy hwin pair past
      input).target .both
  have htarget :=
    profiledRawJointHybridGuardedRightPrefixReceiverAfter_target A strategy
      hwin installation past input
  have hrootTarget := hroot
  rw [profiledRawJointHybridGuardedRightReceiverTargetRoot?_some A strategy
      hwin initialBank _ target htarget,
    profiledRawJointHybridGuardedRightPrefixReceiverAfter_installation]
      at hrootTarget
  have hslot :=
    profiledRawJointHybridMegaGuardedRightTargetRoot?_slot A strategy hwin
      initialBank installation target root hrootTarget
  have hprojection :
      profiledRawJointUnitRightTargetProjection A target =
        .inr (.inr root.2.slot) := by
    simp [profiledRawJointUnitRightTargetProjection, hslot]
  have hclose :=
    profiledRawJointHybridGuardedRightPrefixTargetCloses A strategy hwin
      installation past input .both
  change erasePairedProfiledState A
      (profiledRawJointUnitRightTargetProjection A target) =
    pairedRightCloseTarget A state.2.base.2.1 .both
      (profiledRawJointTargetRightPhysicalLetter A record) at hclose
  rw [hprojection] at hclose
  exact
    pairedCodeStateForRow_both_eq_rightBothStep_selected_current_of_exactTarget
      A root.2.slot state.2.base.2.1 .both
        (profiledRawJointTargetRightPhysicalLetter A record) hclose

/-- Left-prefix / right-root mirror. -/
theorem
    profiledRawJointHybridMegaGuardedLeftPrefixTargetRoot_first_eq_scanCurrent
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (past : List (In₁ × In₂)) (input : In₁ × In₂)
    (root : ProfiledRawJointHybridMegaGuardedLeftTargetRoot A strategy hwin
      initialBank)
    (hroot :
      profiledRawJointHybridGuardedLeftReceiverTargetRoot? A strategy hwin
          initialBank
          (profiledRawJointHybridGuardedLeftPrefixReceiverAfter A strategy
            hwin installation past input) = some root) :
    let pair := profiledRawJointHybridGuardedCommonPairAt A strategy hwin
      installation
    let state := profiledRawJointGuardedCommonLeftFiniteStateAfter A strategy
      hwin pair past
    let monitor := profiledRawJointGuardedLeftPhysicalSiblingMonitor A
      pair.1.2.1 false
    let controller := (pair.1.2).memberController A false
    let record := narrowedRecord monitor (controller.labelOf state.1) state.2
      input
    pairedCodeStateForRow A .first root.2.slot.1.1 =
      (pairedLeftScanPairForRow A .both
        (pairedLeftScanStep A state.2.base.2.1
          (profiledRawJointTargetLeftPhysicalLetter A record))).1 := by
  dsimp only
  let pair := profiledRawJointHybridGuardedCommonPairAt A strategy hwin
    installation
  let state := profiledRawJointGuardedCommonLeftFiniteStateAfter A strategy
    hwin pair past
  let monitor := profiledRawJointGuardedLeftPhysicalSiblingMonitor A
    pair.1.2.1 false
  let controller := (pair.1.2).memberController A false
  let record := narrowedRecord monitor (controller.labelOf state.1) state.2
    input
  let target :=
    (profiledRawJointGuardedCommonLeftPrefixOutput A strategy hwin pair past
      input).target .both
  have htarget :=
    profiledRawJointHybridGuardedLeftPrefixReceiverAfter_target A strategy
      hwin installation past input
  have hrootTarget := hroot
  rw [profiledRawJointHybridGuardedLeftReceiverTargetRoot?_some A strategy
      hwin initialBank _ target htarget,
    profiledRawJointHybridGuardedLeftPrefixReceiverAfter_installation]
      at hrootTarget
  have hslot :=
    profiledRawJointHybridMegaGuardedLeftTargetRoot?_slot A strategy hwin
      initialBank installation target root hrootTarget
  have hprojection :
      profiledRawJointUnitLeftTargetProjection A target =
        .inr (.inl root.2.slot) := by
    simp [profiledRawJointUnitLeftTargetProjection, hslot]
  have hclose :=
    profiledRawJointHybridGuardedLeftPrefixTargetCloses A strategy hwin
      installation past input .both
  change erasePairedProfiledState A
      (profiledRawJointUnitLeftTargetProjection A target) =
    pairedLeftCloseTarget A state.2.base.2.1 .both
      (profiledRawJointTargetLeftPhysicalLetter A record) at hclose
  rw [hprojection] at hclose
  exact
    pairedCodeStateForRow_first_eq_leftScanStep_selected_current_of_exactTarget
      A root.2.slot state.2.base.2.1 .both
        (profiledRawJointTargetLeftPhysicalLetter A record) hclose

/-- Simultaneous left-prefix / right-root checker alignment. -/
theorem
    profiledRawJointHybridMegaGuardedLeftPrefixTargetRoot_both_eq_scanCurrent
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (past : List (In₁ × In₂)) (input : In₁ × In₂)
    (root : ProfiledRawJointHybridMegaGuardedLeftTargetRoot A strategy hwin
      initialBank)
    (hroot :
      profiledRawJointHybridGuardedLeftReceiverTargetRoot? A strategy hwin
          initialBank
          (profiledRawJointHybridGuardedLeftPrefixReceiverAfter A strategy
            hwin installation past input) = some root) :
    let pair := profiledRawJointHybridGuardedCommonPairAt A strategy hwin
      installation
    let state := profiledRawJointGuardedCommonLeftFiniteStateAfter A strategy
      hwin pair past
    let monitor := profiledRawJointGuardedLeftPhysicalSiblingMonitor A
      pair.1.2.1 false
    let controller := (pair.1.2).memberController A false
    let record := narrowedRecord monitor (controller.labelOf state.1) state.2
      input
    pairedCodeStateForRow A .both root.2.slot.1.1 =
      A.step (pairedLeftScanPairForRow A .both state.2.base.2.1).1
        (bothRoundRecord
          (profiledRawJointTargetLeftPhysicalLetter A record).1
          (pairedLeftInformedForRow .both
            (profiledRawJointTargetLeftPhysicalLetter A record).2.1)
          (pairedLeftClosingForRow .both
            (profiledRawJointTargetLeftPhysicalLetter A record).2.1)) := by
  dsimp only
  let pair := profiledRawJointHybridGuardedCommonPairAt A strategy hwin
    installation
  let state := profiledRawJointGuardedCommonLeftFiniteStateAfter A strategy
    hwin pair past
  let monitor := profiledRawJointGuardedLeftPhysicalSiblingMonitor A
    pair.1.2.1 false
  let controller := (pair.1.2).memberController A false
  let record := narrowedRecord monitor (controller.labelOf state.1) state.2
    input
  let target :=
    (profiledRawJointGuardedCommonLeftPrefixOutput A strategy hwin pair past
      input).target .both
  have htarget :=
    profiledRawJointHybridGuardedLeftPrefixReceiverAfter_target A strategy
      hwin installation past input
  have hrootTarget := hroot
  rw [profiledRawJointHybridGuardedLeftReceiverTargetRoot?_some A strategy
      hwin initialBank _ target htarget,
    profiledRawJointHybridGuardedLeftPrefixReceiverAfter_installation]
      at hrootTarget
  have hslot :=
    profiledRawJointHybridMegaGuardedLeftTargetRoot?_slot A strategy hwin
      initialBank installation target root hrootTarget
  have hprojection :
      profiledRawJointUnitLeftTargetProjection A target =
        .inr (.inl root.2.slot) := by
    simp [profiledRawJointUnitLeftTargetProjection, hslot]
  have hclose :=
    profiledRawJointHybridGuardedLeftPrefixTargetCloses A strategy hwin
      installation past input .both
  change erasePairedProfiledState A
      (profiledRawJointUnitLeftTargetProjection A target) =
    pairedLeftCloseTarget A state.2.base.2.1 .both
      (profiledRawJointTargetLeftPhysicalLetter A record) at hclose
  rw [hprojection] at hclose
  exact
    pairedCodeStateForRow_both_eq_leftBothStep_selected_current_of_exactTarget
      A root.2.slot state.2.base.2.1 .both
        (profiledRawJointTargetLeftPhysicalLetter A record) hclose

/-! ## Accepted fixed tails from the literal guarded scan state -/

/-- The guarded-right reversal plus an arbitrary fixed-left tail is accepted
from the actual scan successor, with no checker restart. -/
theorem
    profiledRawJointHybridMegaGuardedLinked_rightPrefix_leftClose_acceptsFrom_scanCurrent
    (controllers :
      ProfiledRawJointRootCompatibleInitialControllers A strategy)
    (fallbackTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
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
    let pair := profiledRawJointHybridGuardedCommonPairAt A strategy hwin
      installation
    let state := profiledRawJointGuardedCommonRightFiniteStateAfter A strategy
      hwin pair past
    let monitor := profiledRawJointGuardedRightPhysicalSiblingMonitor A
      pair.1.1.1 false
    let controller := (pair.1.1).memberController A false
    let record := narrowedRecord monitor (controller.labelOf state.1) state.2
      input
    let mega := MegaGuardedLinkedPhysicalController A strategy hwin
      controllers initialBank fallbackTag
    let env := profiledRawJointUnitStrictLeftEnvironment
      (profiledRawJointHybridMegaGuardedPrependLeftInput
        (nextInputOne, nextInputTwo) tail)
    A.AcceptsFrom
      (pairedRightScanPairForRow A .both
        (pairedRightScanStep A state.2.base.2.1
          (profiledRawJointTargetRightPhysicalLetter A record))).1
      ((mega.globalMachine.reroot
          (profiledRawJointHybridMegaGuardedLinkedRightPrefixControls A
            strategy hwin controllers initialBank fallbackTag installation
              past input oldOutputOne oldOutputTwo)).globalMachineTraceWord
        mega.globalOutputOne mega.globalOutputTwo env) := by
  dsimp only
  rw [←
    profiledRawJointHybridMegaGuardedRightPrefixTargetRoot_first_eq_scanCurrent
      A strategy hwin initialBank installation past input root hroot]
  exact
    profiledRawJointHybridMegaGuardedLinked_rightPrefix_leftClose_acceptsFrom_first
      A strategy hwin controllers initialBank fallbackTag installation past
        input oldOutputOne oldOutputTwo nextInputOne nextInputTwo tail root
          hroot

/-- Fixed-right mirror from the literal guarded-left scan successor. -/
theorem
    profiledRawJointHybridMegaGuardedLinked_leftPrefix_rightClose_acceptsFrom_scanCurrent
    (controllers :
      ProfiledRawJointRootCompatibleInitialControllers A strategy)
    (fallbackTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
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
    let pair := profiledRawJointHybridGuardedCommonPairAt A strategy hwin
      installation
    let state := profiledRawJointGuardedCommonLeftFiniteStateAfter A strategy
      hwin pair past
    let monitor := profiledRawJointGuardedLeftPhysicalSiblingMonitor A
      pair.1.2.1 false
    let controller := (pair.1.2).memberController A false
    let record := narrowedRecord monitor (controller.labelOf state.1) state.2
      input
    let mega := MegaGuardedLinkedPhysicalController A strategy hwin
      controllers initialBank fallbackTag
    let env := profiledRawJointUnitStrictRightEnvironment
      (profiledRawJointHybridMegaGuardedPrependRightInput
        (nextInputTwo, nextInputOne) tail)
    A.AcceptsFrom
      (pairedLeftScanPairForRow A .both
        (pairedLeftScanStep A state.2.base.2.1
          (profiledRawJointTargetLeftPhysicalLetter A record))).1
      ((mega.globalMachine.reroot
          (profiledRawJointHybridMegaGuardedLinkedLeftPrefixControls A
            strategy hwin controllers initialBank fallbackTag installation
              past input oldOutputOne oldOutputTwo)).globalMachineTraceWord
        mega.globalOutputOne mega.globalOutputTwo env) := by
  dsimp only
  rw [←
    profiledRawJointHybridMegaGuardedLeftPrefixTargetRoot_first_eq_scanCurrent
      A strategy hwin initialBank installation past input root hroot]
  exact
    profiledRawJointHybridMegaGuardedLinked_leftPrefix_rightClose_acceptsFrom_first
      A strategy hwin controllers initialBank fallbackTag installation past
        input oldOutputOne oldOutputTwo nextInputOne nextInputTwo tail root
          hroot

end

end DetParityAutomaton

end DistributedSynthesis
