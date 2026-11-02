/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridMegaGuardedLinkedFreshHandoff
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridMegaGuardedCheckerAlignment
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointUnitPersistentStrictAcceptance

/-!
# Persistent-strict acceptance after a guarded mega handoff

The first guarded reversal enters a fresh fixed-policy Unit carrier.  The
same-key recurrent simulation identifies the entire later mega word with the
Unit word, while the persistent strict acceptance theorem handles arbitrary
strict reversals rather than only a forever-fixed orientation.
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

section
omit [Inhabited Out₁] [Inhabited Out₂]

/-- Any literal left root returned by the total root staging function is the
policy's canonical root at `run []`. -/
theorem profiledRawJointHybridMegaLeftRoot?_state_eq_run
    (child : Child A strategy hwin initialBank)
    (root : ProfiledRawJointHybridMegaLeftMacro A strategy hwin initialBank
      child)
    (hroot : profiledRawJointHybridMegaLeftRoot? A strategy hwin initialBank
      child = some root) :
    root.state =
      (profiledRawJointHybridMegaChildPolicy A strategy hwin initialBank child
        ).run [] := by
  unfold profiledRawJointHybridMegaLeftRoot? at hroot
  split at hroot
  · simp_all
  · have hr := Option.some.inj hroot
    rw [← hr]
    rfl

/-- Right-root mirror. -/
theorem profiledRawJointHybridMegaRightRoot?_state_eq_run
    (child : Child A strategy hwin initialBank)
    (root : ProfiledRawJointHybridMegaRightMacro A strategy hwin initialBank
      child)
    (hroot : profiledRawJointHybridMegaRightRoot? A strategy hwin initialBank
      child = some root) :
    root.state =
      (profiledRawJointHybridMegaChildPolicy A strategy hwin initialBank child
        ).run [] := by
  unfold profiledRawJointHybridMegaRightRoot? at hroot
  split at hroot
  · simp_all
  · have hr := Option.some.inj hroot
    rw [← hr]
    rfl

/-- A successful checked guarded-right target lookup returns a canonical
left policy root. -/
theorem profiledRawJointHybridMegaGuardedRightTargetRoot?_state_eq_run
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (target : ProfiledRawJointUnitTarget A)
    (root : ProfiledRawJointHybridMegaGuardedRightTargetRoot A strategy hwin
      initialBank)
    (hroot :
      profiledRawJointHybridMegaGuardedRightTargetRoot? A strategy hwin
        initialBank installation target = some root) :
    root.2.state =
      (profiledRawJointHybridMegaChildPolicy A strategy hwin initialBank root.1
        ).run [] := by
  unfold profiledRawJointHybridMegaGuardedRightTargetRoot? at hroot
  split at hroot
  · simp_all
  · rename_i child hchild
    split at hroot
    · simp_all
    · rename_i staged hstaged
      have hpair : (⟨child, staged⟩ :
          ProfiledRawJointHybridMegaGuardedRightTargetRoot A strategy hwin
            initialBank) = root := Option.some.inj hroot
      cases hpair
      exact profiledRawJointHybridMegaLeftRoot?_state_eq_run A strategy hwin
        initialBank child staged hstaged

/-- Checked guarded-left mirror. -/
theorem profiledRawJointHybridMegaGuardedLeftTargetRoot?_state_eq_run
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (target : ProfiledRawJointUnitTarget A)
    (root : ProfiledRawJointHybridMegaGuardedLeftTargetRoot A strategy hwin
      initialBank)
    (hroot :
      profiledRawJointHybridMegaGuardedLeftTargetRoot? A strategy hwin
        initialBank installation target = some root) :
    root.2.state =
      (profiledRawJointHybridMegaChildPolicy A strategy hwin initialBank root.1
        ).run [] := by
  unfold profiledRawJointHybridMegaGuardedLeftTargetRoot? at hroot
  split at hroot
  · simp_all
  · rename_i child hchild
    split at hroot
    · simp_all
    · rename_i staged hstaged
      have hpair : (⟨child, staged⟩ :
          ProfiledRawJointHybridMegaGuardedLeftTargetRoot A strategy hwin
            initialBank) = root := Option.some.inj hroot
      cases hpair
      exact profiledRawJointHybridMegaRightRoot?_state_eq_run A strategy hwin
        initialBank child staged hstaged

end

/-- Successful target lookup through a live guarded-right receiver likewise
returns the canonical child-policy root. -/
theorem profiledRawJointHybridGuardedRightReceiverTargetRoot?_state_eq_run
    (state : ProfiledRawJointHybridGuardedRightInstalledReceiver A strategy
      hwin)
    (root : ProfiledRawJointHybridMegaGuardedRightTargetRoot A strategy hwin
      initialBank)
    (hroot :
      profiledRawJointHybridGuardedRightReceiverTargetRoot? A strategy hwin
        initialBank state = some root) :
    root.2.state =
      (profiledRawJointHybridMegaChildPolicy A strategy hwin initialBank root.1
        ).run [] := by
  unfold profiledRawJointHybridGuardedRightReceiverTargetRoot? at hroot
  split at hroot
  · simp_all
  · rename_i target htarget
    exact profiledRawJointHybridMegaGuardedRightTargetRoot?_state_eq_run A
      strategy hwin initialBank state.1 target root hroot

/-- Guarded-left receiver mirror. -/
theorem profiledRawJointHybridGuardedLeftReceiverTargetRoot?_state_eq_run
    (state : ProfiledRawJointHybridGuardedLeftInstalledReceiver A strategy
      hwin)
    (root : ProfiledRawJointHybridMegaGuardedLeftTargetRoot A strategy hwin
      initialBank)
    (hroot :
      profiledRawJointHybridGuardedLeftReceiverTargetRoot? A strategy hwin
        initialBank state = some root) :
    root.2.state =
      (profiledRawJointHybridMegaChildPolicy A strategy hwin initialBank root.1
        ).run [] := by
  unfold profiledRawJointHybridGuardedLeftReceiverTargetRoot? at hroot
  split at hroot
  · simp_all
  · rename_i target htarget
    exact profiledRawJointHybridMegaGuardedLeftTargetRoot?_state_eq_run A
      strategy hwin initialBank state.1 target root hroot

/-- The strict guarded-right close splices to the fresh matched-left Unit word
for any physical environment with the prescribed first left round. -/
theorem
    profiledRawJointHybridMegaGuardedLinked_rightPrefix_leftClose_traceWord_eq_fresh_of_head
    (fallbackTag : RetainedTag A strategy hwin)
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (nextInputOne : In₁) (nextInputTwo : In₂)
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (hhead : physicalEnv 0 = ⟨nextInputOne, nextInputTwo, .left⟩)
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
    ((Mega A strategy hwin controllers initialBank fallbackTag).globalMachine
        |>.reroot
          (profiledRawJointHybridMegaGuardedLinkedRightPrefixControls A
            strategy hwin controllers initialBank fallbackTag installation
              past input oldOutputOne oldOutputTwo)).globalMachineTraceWord
        (Mega A strategy hwin controllers initialBank fallbackTag
          ).globalOutputOne
        (Mega A strategy hwin controllers initialBank fallbackTag
          ).globalOutputTwo physicalEnv =
      (unit.globalMachine.reroot fresh).globalMachineTraceWord
        unit.globalOutputOne unit.globalOutputTwo physicalEnv := by
  classical
  dsimp only
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
          .first oldOutputOne oldOutputTwo) physicalEnv
  simpa [hhead] using
    (profiledRawJointHybridMegaGuardedLinked_rightPrefix_leftClose_fresh A
      strategy hwin controllers initialBank fallbackTag installation past
        input oldOutputOne oldOutputTwo nextInputOne nextInputTwo root hroot)

/-- A checked guarded-right close followed by any terminating all-strict tail
is accepted from the target's exact `.first` checker coordinate. -/
theorem
    profiledRawJointHybridMegaGuardedLinked_rightPrefix_leftClose_persistentStrict_acceptsFrom_first
    (fallbackTag : RetainedTag A strategy hwin)
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (nextInputOne : In₁) (nextInputTwo : In₂)
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (hhead : physicalEnv 0 = ⟨nextInputOne, nextInputTwo, .left⟩)
    (hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv 0))
    (hnoboth : ∀ n : Nat,
      profiledRawJointPhysicalGraphTail physicalEnv 0 n ≠ .both)
    (root : ProfiledRawJointHybridMegaGuardedRightTargetRoot A strategy hwin
      initialBank)
    (hroot :
      profiledRawJointHybridGuardedRightReceiverTargetRoot? A strategy hwin
          initialBank
          (profiledRawJointHybridGuardedRightPrefixReceiverAfter A strategy
            hwin installation past input) = some root) :
    let mega := Mega A strategy hwin controllers initialBank fallbackTag
    A.AcceptsFrom (pairedCodeStateForRow A .first root.2.slot.1.1)
      ((mega.globalMachine.reroot
          (profiledRawJointHybridMegaGuardedLinkedRightPrefixControls A
            strategy hwin controllers initialBank fallbackTag installation
              past input oldOutputOne oldOutputTwo)).globalMachineTraceWord
        mega.globalOutputOne mega.globalOutputTwo physicalEnv) := by
  dsimp only
  rw [profiledRawJointHybridMegaGuardedLinked_rightPrefix_leftClose_traceWord_eq_fresh_of_head
    A strategy hwin controllers initialBank fallbackTag installation past input
      oldOutputOne oldOutputTwo nextInputOne nextInputTwo physicalEnv hhead root
        hroot]
  have hgraph : (physicalEnv 0).graph = .left := by
    simpa using congrArg EnvironmentRound.graph hhead
  have hseed :=
    profiledRawJointHybridGuardedRightReceiverTargetRoot?_state_eq_run A
      strategy hwin initialBank
        (profiledRawJointHybridGuardedRightPrefixReceiverAfter A strategy hwin
          installation past input) root hroot
  exact profiledRawJointUnitFreshMatchedLeft_persistentStrict_acceptsFrom A
    strategy
      (profiledRawJointHybridMegaChildSource A strategy hwin initialBank root.1)
      (profiledRawJointHybridMegaChildPolicy A strategy hwin initialBank root.1)
      (profiledRawJointHybridMegaChildControllerBank A strategy hwin initialBank
        root.1)
      (UnitAdapter A strategy hwin controllers initialBank root.1) root.2
      oldOutputOne oldOutputTwo physicalEnv hterm hnoboth hgraph hseed

/-- Guarded-left / fresh matched-right whole-word splice for an arbitrary
physical environment with the prescribed first right round. -/
theorem
    profiledRawJointHybridMegaGuardedLinked_leftPrefix_rightClose_traceWord_eq_fresh_of_head
    (fallbackTag : RetainedTag A strategy hwin)
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (past : List (In₁ × In₂)) (input : In₁ × In₂)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (nextInputOne : In₁) (nextInputTwo : In₂)
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (hhead : physicalEnv 0 = ⟨nextInputOne, nextInputTwo, .right⟩)
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
    ((Mega A strategy hwin controllers initialBank fallbackTag).globalMachine
        |>.reroot
          (profiledRawJointHybridMegaGuardedLinkedLeftPrefixControls A
            strategy hwin controllers initialBank fallbackTag installation
              past input oldOutputOne oldOutputTwo)).globalMachineTraceWord
        (Mega A strategy hwin controllers initialBank fallbackTag
          ).globalOutputOne
        (Mega A strategy hwin controllers initialBank fallbackTag
          ).globalOutputTwo physicalEnv =
      (unit.globalMachine.reroot fresh).globalMachineTraceWord
        unit.globalOutputOne unit.globalOutputTwo physicalEnv := by
  classical
  dsimp only
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
          .first oldOutputOne oldOutputTwo) physicalEnv
  simpa [hhead] using
    (profiledRawJointHybridMegaGuardedLinked_leftPrefix_rightClose_fresh A
      strategy hwin controllers initialBank fallbackTag installation past
        input oldOutputOne oldOutputTwo nextInputOne nextInputTwo root hroot)

/-- Guarded-left mirror of persistent-strict acceptance. -/
theorem
    profiledRawJointHybridMegaGuardedLinked_leftPrefix_rightClose_persistentStrict_acceptsFrom_first
    (fallbackTag : RetainedTag A strategy hwin)
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (past : List (In₁ × In₂)) (input : In₁ × In₂)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (nextInputOne : In₁) (nextInputTwo : In₂)
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (hhead : physicalEnv 0 = ⟨nextInputOne, nextInputTwo, .right⟩)
    (hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv 0))
    (hnoboth : ∀ n : Nat,
      profiledRawJointPhysicalGraphTail physicalEnv 0 n ≠ .both)
    (root : ProfiledRawJointHybridMegaGuardedLeftTargetRoot A strategy hwin
      initialBank)
    (hroot :
      profiledRawJointHybridGuardedLeftReceiverTargetRoot? A strategy hwin
          initialBank
          (profiledRawJointHybridGuardedLeftPrefixReceiverAfter A strategy
            hwin installation past input) = some root) :
    let mega := Mega A strategy hwin controllers initialBank fallbackTag
    A.AcceptsFrom (pairedCodeStateForRow A .first root.2.slot.1.1)
      ((mega.globalMachine.reroot
          (profiledRawJointHybridMegaGuardedLinkedLeftPrefixControls A
            strategy hwin controllers initialBank fallbackTag installation
              past input oldOutputOne oldOutputTwo)).globalMachineTraceWord
        mega.globalOutputOne mega.globalOutputTwo physicalEnv) := by
  dsimp only
  rw [profiledRawJointHybridMegaGuardedLinked_leftPrefix_rightClose_traceWord_eq_fresh_of_head
    A strategy hwin controllers initialBank fallbackTag installation past input
      oldOutputOne oldOutputTwo nextInputOne nextInputTwo physicalEnv hhead root
        hroot]
  have hgraph : (physicalEnv 0).graph = .right := by
    simpa using congrArg EnvironmentRound.graph hhead
  have hseed :=
    profiledRawJointHybridGuardedLeftReceiverTargetRoot?_state_eq_run A
      strategy hwin initialBank
        (profiledRawJointHybridGuardedLeftPrefixReceiverAfter A strategy hwin
          installation past input) root hroot
  exact profiledRawJointUnitFreshMatchedRight_persistentStrict_acceptsFrom A
    strategy
      (profiledRawJointHybridMegaChildSource A strategy hwin initialBank root.1)
      (profiledRawJointHybridMegaChildPolicy A strategy hwin initialBank root.1)
      (profiledRawJointHybridMegaChildControllerBank A strategy hwin initialBank
        root.1)
      (UnitAdapter A strategy hwin controllers initialBank root.1) root.2
      oldOutputOne oldOutputTwo physicalEnv hterm hnoboth hgraph hseed

/-! ## Literal scan-state and actual-prefix closures -/

/-- The guarded-right persistent-strict suffix is accepted from the literal
checker state reached by the finite guarded scan. -/
theorem
    profiledRawJointHybridMegaGuardedLinked_rightPrefix_leftClose_persistentStrict_acceptsFrom_scanCurrent
    (fallbackTag : RetainedTag A strategy hwin)
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (nextInputOne : In₁) (nextInputTwo : In₂)
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (hhead : physicalEnv 0 = ⟨nextInputOne, nextInputTwo, .left⟩)
    (hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv 0))
    (hnoboth : ∀ n : Nat,
      profiledRawJointPhysicalGraphTail physicalEnv 0 n ≠ .both)
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
    let mega := Mega A strategy hwin controllers initialBank fallbackTag
    A.AcceptsFrom
      (pairedRightScanPairForRow A .both
        (pairedRightScanStep A state.2.base.2.1
          (profiledRawJointTargetRightPhysicalLetter A record))).1
      ((mega.globalMachine.reroot
          (profiledRawJointHybridMegaGuardedLinkedRightPrefixControls A
            strategy hwin controllers initialBank fallbackTag installation
              past input oldOutputOne oldOutputTwo)).globalMachineTraceWord
        mega.globalOutputOne mega.globalOutputTwo physicalEnv) := by
  dsimp only
  rw [←
    profiledRawJointHybridMegaGuardedRightPrefixTargetRoot_first_eq_scanCurrent
      A strategy hwin initialBank installation past input root hroot]
  exact
    profiledRawJointHybridMegaGuardedLinked_rightPrefix_leftClose_persistentStrict_acceptsFrom_first
      A strategy hwin controllers initialBank fallbackTag installation past
        input oldOutputOne oldOutputTwo nextInputOne nextInputTwo physicalEnv
          hhead hterm hnoboth root hroot

/-- Guarded-left mirror from the literal finite-scan checker state. -/
theorem
    profiledRawJointHybridMegaGuardedLinked_leftPrefix_rightClose_persistentStrict_acceptsFrom_scanCurrent
    (fallbackTag : RetainedTag A strategy hwin)
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (past : List (In₁ × In₂)) (input : In₁ × In₂)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (nextInputOne : In₁) (nextInputTwo : In₂)
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (hhead : physicalEnv 0 = ⟨nextInputOne, nextInputTwo, .right⟩)
    (hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv 0))
    (hnoboth : ∀ n : Nat,
      profiledRawJointPhysicalGraphTail physicalEnv 0 n ≠ .both)
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
    let mega := Mega A strategy hwin controllers initialBank fallbackTag
    A.AcceptsFrom
      (pairedLeftScanPairForRow A .both
        (pairedLeftScanStep A state.2.base.2.1
          (profiledRawJointTargetLeftPhysicalLetter A record))).1
      ((mega.globalMachine.reroot
          (profiledRawJointHybridMegaGuardedLinkedLeftPrefixControls A
            strategy hwin controllers initialBank fallbackTag installation
              past input oldOutputOne oldOutputTwo)).globalMachineTraceWord
        mega.globalOutputOne mega.globalOutputTwo physicalEnv) := by
  dsimp only
  rw [←
    profiledRawJointHybridMegaGuardedLeftPrefixTargetRoot_first_eq_scanCurrent
      A strategy hwin initialBank installation past input root hroot]
  exact
    profiledRawJointHybridMegaGuardedLinked_leftPrefix_rightClose_persistentStrict_acceptsFrom_first
      A strategy hwin controllers initialBank fallbackTag installation past
        input oldOutputOne oldOutputTwo nextInputOne nextInputTwo physicalEnv
          hhead hterm hnoboth root hroot

/-- If the actual mega run reaches a guarded-right prefix with the literal
scan checker state, the first strict-left close and its arbitrary all-strict
tail imply acceptance of the complete physical word. -/
theorem
    profiledRawJointHybridMegaGuardedLinked_accepts_of_rightPrefix_leftClose_persistentStrict
    (fallbackTag : RetainedTag A strategy hwin)
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (env : EnvironmentSequence In₁ In₂) (start : Nat)
    (nextInputOne : In₁) (nextInputTwo : In₂)
    (hhead : env start = ⟨nextInputOne, nextInputTwo, .left⟩)
    (hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail (OmegaWord.drop env start) 0))
    (hnoboth : ∀ n : Nat,
      profiledRawJointPhysicalGraphTail (OmegaWord.drop env start) 0 n ≠
        .both)
    (root : ProfiledRawJointHybridMegaGuardedRightTargetRoot A strategy hwin
      initialBank)
    (hroot :
      profiledRawJointHybridGuardedRightReceiverTargetRoot? A strategy hwin
          initialBank
          (profiledRawJointHybridGuardedRightPrefixReceiverAfter A strategy
            hwin installation past input) = some root)
    (hphysical :
      let mega := Mega A strategy hwin controllers initialBank fallbackTag
      mega.globalMachine.globalStateTrace env start =
        profiledRawJointHybridMegaGuardedLinkedRightPrefixControls A strategy
          hwin controllers initialBank fallbackTag installation past input
            oldOutputOne oldOutputTwo)
    (hchecker :
      let pair := profiledRawJointHybridGuardedCommonPairAt A strategy hwin
        installation
      let state := profiledRawJointGuardedCommonRightFiniteStateAfter A
        strategy hwin pair past
      let monitor := profiledRawJointGuardedRightPhysicalSiblingMonitor A
        pair.1.1.1 false
      let controller := (pair.1.1).memberController A false
      let record := narrowedRecord monitor (controller.labelOf state.1) state.2
        input
      let mega := Mega A strategy hwin controllers initialBank fallbackTag
      A.run
          (mega.globalMachine.globalMachineTraceWord mega.globalOutputOne
            mega.globalOutputTwo env) start =
        (pairedRightScanPairForRow A .both
          (pairedRightScanStep A state.2.base.2.1
            (profiledRawJointTargetRightPhysicalLetter A record))).1) :
    let mega := Mega A strategy hwin controllers initialBank fallbackTag
    A.Accepts
      (mega.globalMachine.globalMachineTraceWord mega.globalOutputOne
        mega.globalOutputTwo env) := by
  dsimp only at hphysical hchecker ⊢
  let mega := Mega A strategy hwin controllers initialBank fallbackTag
  apply A.accepts_of_rerootedGlobalMachine_acceptsFrom mega.globalMachine
    mega.globalOutputOne mega.globalOutputTwo env start
  rw [hphysical, hchecker]
  apply
    profiledRawJointHybridMegaGuardedLinked_rightPrefix_leftClose_persistentStrict_acceptsFrom_scanCurrent
      A strategy hwin controllers initialBank fallbackTag installation past
        input oldOutputOne oldOutputTwo nextInputOne nextInputTwo
          (OmegaWord.drop env start) (root := root)
  · simpa [OmegaWord.drop] using hhead
  · exact hterm
  · exact hnoboth
  · exact hroot

/-- Actual-prefix mirror for a guarded-left block closed by a strict-right
round. -/
theorem
    profiledRawJointHybridMegaGuardedLinked_accepts_of_leftPrefix_rightClose_persistentStrict
    (fallbackTag : RetainedTag A strategy hwin)
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (past : List (In₁ × In₂)) (input : In₁ × In₂)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (env : EnvironmentSequence In₁ In₂) (start : Nat)
    (nextInputOne : In₁) (nextInputTwo : In₂)
    (hhead : env start = ⟨nextInputOne, nextInputTwo, .right⟩)
    (hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail (OmegaWord.drop env start) 0))
    (hnoboth : ∀ n : Nat,
      profiledRawJointPhysicalGraphTail (OmegaWord.drop env start) 0 n ≠
        .both)
    (root : ProfiledRawJointHybridMegaGuardedLeftTargetRoot A strategy hwin
      initialBank)
    (hroot :
      profiledRawJointHybridGuardedLeftReceiverTargetRoot? A strategy hwin
          initialBank
          (profiledRawJointHybridGuardedLeftPrefixReceiverAfter A strategy
            hwin installation past input) = some root)
    (hphysical :
      let mega := Mega A strategy hwin controllers initialBank fallbackTag
      mega.globalMachine.globalStateTrace env start =
        profiledRawJointHybridMegaGuardedLinkedLeftPrefixControls A strategy
          hwin controllers initialBank fallbackTag installation past input
            oldOutputOne oldOutputTwo)
    (hchecker :
      let pair := profiledRawJointHybridGuardedCommonPairAt A strategy hwin
        installation
      let state := profiledRawJointGuardedCommonLeftFiniteStateAfter A strategy
        hwin pair past
      let monitor := profiledRawJointGuardedLeftPhysicalSiblingMonitor A
        pair.1.2.1 false
      let controller := (pair.1.2).memberController A false
      let record := narrowedRecord monitor (controller.labelOf state.1) state.2
        input
      let mega := Mega A strategy hwin controllers initialBank fallbackTag
      A.run
          (mega.globalMachine.globalMachineTraceWord mega.globalOutputOne
            mega.globalOutputTwo env) start =
        (pairedLeftScanPairForRow A .both
          (pairedLeftScanStep A state.2.base.2.1
            (profiledRawJointTargetLeftPhysicalLetter A record))).1) :
    let mega := Mega A strategy hwin controllers initialBank fallbackTag
    A.Accepts
      (mega.globalMachine.globalMachineTraceWord mega.globalOutputOne
        mega.globalOutputTwo env) := by
  dsimp only at hphysical hchecker ⊢
  let mega := Mega A strategy hwin controllers initialBank fallbackTag
  apply A.accepts_of_rerootedGlobalMachine_acceptsFrom mega.globalMachine
    mega.globalOutputOne mega.globalOutputTwo env start
  rw [hphysical, hchecker]
  apply
    profiledRawJointHybridMegaGuardedLinked_leftPrefix_rightClose_persistentStrict_acceptsFrom_scanCurrent
      A strategy hwin controllers initialBank fallbackTag installation past
        input oldOutputOne oldOutputTwo nextInputOne nextInputTwo
          (OmegaWord.drop env start) (root := root)
  · simpa [OmegaWord.drop] using hhead
  · exact hterm
  · exact hnoboth
  · exact hroot

end

end DetParityAutomaton

end DistributedSynthesis
