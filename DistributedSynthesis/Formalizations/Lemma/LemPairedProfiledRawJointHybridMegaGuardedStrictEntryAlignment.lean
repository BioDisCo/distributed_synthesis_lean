/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridMegaGuardedLinkedPersistentStrictAcceptance
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonTailCoreStrictAcceptance

/-!
# Exact checker alignment through a guarded strict entry

The guarded target checker is initialized by the represented common slot.
This file threads that concrete DPA state through every literal strict-prefix
record.  Thus the scan coordinate used by the fresh handoff is the actual
checker state, rather than a priority-equivalent or clock-shifted surrogate.
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

private abbrev CommonPair :=
  ProfiledRawJointGuardedCommonPair A strategy hwin

/-- If the physical word enters a guarded-right block at the represented
`.both` source and contains the literal controller prefix, its checker after
that prefix is exactly the guarded scan current stored by the finite state. -/
theorem profiledRawJointGuardedCommonRight_run_add_eq_scanCurrent
    (pair : CommonPair A strategy hwin)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (start : Nat)
    (hentry : A.run word start =
      pairedCodeStateForRow A .both pair.1.1.1.base.source.1.1)
    (hslice :
      let monitor := profiledRawJointGuardedRightPhysicalSiblingMonitor A
        pair.1.1.1 false
      let controller := (pair.1.1).memberController A false
      let localEnv : Nat → In₂ × In₁ := omegaOfList (past ++ [input])
      let play := treePlay
        (narrowedInducedTree monitor controller.labeledTree) localEnv
      omegaPrefix (OmegaWord.drop word start)
          (profiledRawJointTargetRightPhysicalPrefixRecords A .both
            (omegaPrefix play (past.length + 1))).length =
        profiledRawJointTargetRightPhysicalPrefixRecords A .both
          (omegaPrefix play (past.length + 1))) :
    let state := profiledRawJointGuardedCommonRightFiniteStateAfter A strategy
      hwin pair past
    let monitor := profiledRawJointGuardedRightPhysicalSiblingMonitor A
      pair.1.1.1 false
    let controller := (pair.1.1).memberController A false
    let record := narrowedRecord monitor (controller.labelOf state.1) state.2
      input
    let localEnv : Nat → In₂ × In₁ := omegaOfList (past ++ [input])
    let play := treePlay
      (narrowedInducedTree monitor controller.labeledTree) localEnv
    A.run word
        (start +
          (profiledRawJointTargetRightPhysicalPrefixRecords A .both
            (omegaPrefix play (past.length + 1))).length) =
      (pairedRightScanPairForRow A .both
        (pairedRightScanStep A state.2.base.2.1
          (profiledRawJointTargetRightPhysicalLetter A record))).1 := by
  dsimp only at hslice ⊢
  let monitor := profiledRawJointGuardedRightPhysicalSiblingMonitor A
    pair.1.1.1 false
  let base := profiledRawJointRightPhysicalSiblingMonitor A
    pair.1.1.1.base false
  let controller := (pair.1.1).memberController A false
  let localEnv : Nat → In₂ × In₁ := omegaOfList (past ++ [input])
  let play := treePlay
    (narrowedInducedTree monitor controller.labeledTree) localEnv
  let state := profiledRawJointGuardedCommonRightFiniteStateAfter A strategy
    hwin pair past
  let record := narrowedRecord monitor (controller.labelOf state.1) state.2
    input
  have hrunGuard :=
    profiledRawJointGuardedCommonRightFiniteStateAfter_monitorRun A strategy
      hwin pair past input
  change monitor.run play past.length = state.2 at hrunGuard
  have hrunBase : base.run play past.length = state.2.base := by
    rw [← BlockRecordMonitor.firstLetterGuard_run_base base
      pair.1.1.1.firstAllowed play past.length]
    exact congrArg (fun guardState ↦ guardState.base) hrunGuard
  have halign :=
    profiledRawJointTargetRight_run_add_eq_scanCurrent_of_slice A
      (profiledRawJointUnitRightTargetProjection A)
      (profiledRawJointRightPhysicalSiblingAllowed A pair.1.1.1.base)
      pair.1.1.1.base.source play (past.length + 1) .both word start hentry
        hslice
  change A.run word
      (start +
        (profiledRawJointTargetRightPhysicalPrefixRecords A .both
          (omegaPrefix play (past.length + 1))).length) =
    (pairedRightScanPairForRow A .both
      (pairedRightScanStep A state.2.base.2.1
        (profiledRawJointTargetRightPhysicalLetter A record))).1
  rw [BlockRecordMonitor.run, hrunBase] at halign
  change _ = (pairedRightScanPairForRow A .both
    (pairedRightScanStep A state.2.base.2.1
      (profiledRawJointTargetRightPhysicalLetter A (play past.length)))).1
    at halign
  have hat :=
    profiledRawJointGuardedCommonRightLiteralPlay_at_prefix A strategy hwin
      pair past input
  change play past.length = record at hat
  rw [hat] at halign
  exact halign

/-- Guarded-left mirror: the actual checker after the literal strict-left
prefix is the finite monitor's current scan coordinate. -/
theorem profiledRawJointGuardedCommonLeft_run_add_eq_scanCurrent
    (pair : CommonPair A strategy hwin)
    (past : List (In₁ × In₂)) (input : In₁ × In₂)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (start : Nat)
    (hentry : A.run word start =
      pairedCodeStateForRow A .both pair.1.2.1.base.source.1.1)
    (hslice :
      let monitor := profiledRawJointGuardedLeftPhysicalSiblingMonitor A
        pair.1.2.1 false
      let controller := (pair.1.2).memberController A false
      let localEnv : Nat → In₁ × In₂ := omegaOfList (past ++ [input])
      let play := treePlay
        (narrowedInducedTree monitor controller.labeledTree) localEnv
      omegaPrefix (OmegaWord.drop word start)
          (profiledRawJointTargetLeftPhysicalPrefixRecords A .both
            (omegaPrefix play (past.length + 1))).length =
        profiledRawJointTargetLeftPhysicalPrefixRecords A .both
          (omegaPrefix play (past.length + 1))) :
    let state := profiledRawJointGuardedCommonLeftFiniteStateAfter A strategy
      hwin pair past
    let monitor := profiledRawJointGuardedLeftPhysicalSiblingMonitor A
      pair.1.2.1 false
    let controller := (pair.1.2).memberController A false
    let record := narrowedRecord monitor (controller.labelOf state.1) state.2
      input
    let localEnv : Nat → In₁ × In₂ := omegaOfList (past ++ [input])
    let play := treePlay
      (narrowedInducedTree monitor controller.labeledTree) localEnv
    A.run word
        (start +
          (profiledRawJointTargetLeftPhysicalPrefixRecords A .both
            (omegaPrefix play (past.length + 1))).length) =
      (pairedLeftScanPairForRow A .both
        (pairedLeftScanStep A state.2.base.2.1
          (profiledRawJointTargetLeftPhysicalLetter A record))).1 := by
  dsimp only at hslice ⊢
  let monitor := profiledRawJointGuardedLeftPhysicalSiblingMonitor A
    pair.1.2.1 false
  let base := profiledRawJointLeftPhysicalSiblingMonitor A
    pair.1.2.1.base false
  let controller := (pair.1.2).memberController A false
  let localEnv : Nat → In₁ × In₂ := omegaOfList (past ++ [input])
  let play := treePlay
    (narrowedInducedTree monitor controller.labeledTree) localEnv
  let state := profiledRawJointGuardedCommonLeftFiniteStateAfter A strategy
    hwin pair past
  let record := narrowedRecord monitor (controller.labelOf state.1) state.2
    input
  have hrunGuard :=
    profiledRawJointGuardedCommonLeftFiniteStateAfter_monitorRun A strategy
      hwin pair past input
  change monitor.run play past.length = state.2 at hrunGuard
  have hrunBase : base.run play past.length = state.2.base := by
    rw [← BlockRecordMonitor.firstLetterGuard_run_base base
      pair.1.2.1.firstAllowed play past.length]
    exact congrArg (fun guardState ↦ guardState.base) hrunGuard
  have halign :=
    profiledRawJointTargetLeft_run_add_eq_scanCurrent_of_slice A
      (profiledRawJointUnitLeftTargetProjection A)
      (profiledRawJointLeftPhysicalSiblingAllowed A pair.1.2.1.base)
      pair.1.2.1.base.source play (past.length + 1) .both word start hentry
        hslice
  change A.run word
      (start +
        (profiledRawJointTargetLeftPhysicalPrefixRecords A .both
          (omegaPrefix play (past.length + 1))).length) =
    (pairedLeftScanPairForRow A .both
      (pairedLeftScanStep A state.2.base.2.1
        (profiledRawJointTargetLeftPhysicalLetter A record))).1
  rw [BlockRecordMonitor.run, hrunBase] at halign
  change _ = (pairedLeftScanPairForRow A .both
    (pairedLeftScanStep A state.2.base.2.1
      (profiledRawJointTargetLeftPhysicalLetter A (play past.length)))).1
    at halign
  have hat :=
    profiledRawJointGuardedCommonLeftLiteralPlay_at_prefix A strategy hwin pair
      past input
  change play past.length = record at hat
  rw [hat] at halign
  exact halign

/-- Infinite-input form of the right scan alignment.  This avoids any
extension choice after the finite prefix and is the form used at an actual
mega cut. -/
theorem profiledRawJointGuardedCommonRight_run_add_eq_scanCurrent_at
    (pair : CommonPair A strategy hwin) (inputs : Nat → In₂ × In₁)
    (n : Nat)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (start : Nat)
    (hentry : A.run word start =
      pairedCodeStateForRow A .both pair.1.1.1.base.source.1.1)
    (hslice :
      let monitor := profiledRawJointGuardedRightPhysicalSiblingMonitor A
        pair.1.1.1 false
      let controller := (pair.1.1).memberController A false
      let play := treePlay
        (narrowedInducedTree monitor controller.labeledTree) inputs
      omegaPrefix (OmegaWord.drop word start)
          (profiledRawJointTargetRightPhysicalPrefixRecords A .both
            (omegaPrefix play (n + 1))).length =
        profiledRawJointTargetRightPhysicalPrefixRecords A .both
          (omegaPrefix play (n + 1))) :
    let state := profiledRawJointGuardedCommonRightFiniteStateAfter A strategy
      hwin pair (omegaPrefix inputs n)
    let monitor := profiledRawJointGuardedRightPhysicalSiblingMonitor A
      pair.1.1.1 false
    let controller := (pair.1.1).memberController A false
    let record := narrowedRecord monitor (controller.labelOf state.1) state.2
      (inputs n)
    let play := treePlay
      (narrowedInducedTree monitor controller.labeledTree) inputs
    A.run word
        (start +
          (profiledRawJointTargetRightPhysicalPrefixRecords A .both
            (omegaPrefix play (n + 1))).length) =
      (pairedRightScanPairForRow A .both
        (pairedRightScanStep A state.2.base.2.1
          (profiledRawJointTargetRightPhysicalLetter A record))).1 := by
  dsimp only at hslice ⊢
  let monitor := profiledRawJointGuardedRightPhysicalSiblingMonitor A
    pair.1.1.1 false
  let base := profiledRawJointRightPhysicalSiblingMonitor A
    pair.1.1.1.base false
  let controller := (pair.1.1).memberController A false
  let play := treePlay
    (narrowedInducedTree monitor controller.labeledTree) inputs
  let state := profiledRawJointGuardedCommonRightFiniteStateAfter A strategy
    hwin pair (omegaPrefix inputs n)
  let record := narrowedRecord monitor (controller.labelOf state.1) state.2
    (inputs n)
  have hrunGuard : monitor.run play n = state.2 := by
    unfold state
    rw [profiledRawJointGuardedCommonRightFiniteStateAfter_eq A strategy hwin]
    rw [← monitor.lift_control_branchNode
      (narrowedInducedTree monitor controller.labeledTree) inputs,
      lift_control_narrowedInducedTree, branchNode_eq_omegaPrefix]
  have hrunBase : base.run play n = state.2.base := by
    rw [← BlockRecordMonitor.firstLetterGuard_run_base base
      pair.1.1.1.firstAllowed play n]
    exact congrArg (fun guardState ↦ guardState.base) hrunGuard
  have halign :=
    profiledRawJointTargetRight_run_add_eq_scanCurrent_of_slice A
      (profiledRawJointUnitRightTargetProjection A)
      (profiledRawJointRightPhysicalSiblingAllowed A pair.1.1.1.base)
      pair.1.1.1.base.source play (n + 1) .both word start hentry hslice
  change A.run word
      (start +
        (profiledRawJointTargetRightPhysicalPrefixRecords A .both
          (omegaPrefix play (n + 1))).length) =
    (pairedRightScanPairForRow A .both
      (pairedRightScanStep A state.2.base.2.1
        (profiledRawJointTargetRightPhysicalLetter A record))).1
  rw [BlockRecordMonitor.run, hrunBase] at halign
  change _ = (pairedRightScanPairForRow A .both
    (pairedRightScanStep A state.2.base.2.1
      (profiledRawJointTargetRightPhysicalLetter A (play n)))).1 at halign
  have hat := profiledRawJointGuardedCommonRightLiteralPlay_at A strategy hwin
    pair inputs n
  change play n = record at hat
  rw [hat] at halign
  exact halign

/-- Infinite-input left mirror of exact scan alignment. -/
theorem profiledRawJointGuardedCommonLeft_run_add_eq_scanCurrent_at
    (pair : CommonPair A strategy hwin) (inputs : Nat → In₁ × In₂)
    (n : Nat)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (start : Nat)
    (hentry : A.run word start =
      pairedCodeStateForRow A .both pair.1.2.1.base.source.1.1)
    (hslice :
      let monitor := profiledRawJointGuardedLeftPhysicalSiblingMonitor A
        pair.1.2.1 false
      let controller := (pair.1.2).memberController A false
      let play := treePlay
        (narrowedInducedTree monitor controller.labeledTree) inputs
      omegaPrefix (OmegaWord.drop word start)
          (profiledRawJointTargetLeftPhysicalPrefixRecords A .both
            (omegaPrefix play (n + 1))).length =
        profiledRawJointTargetLeftPhysicalPrefixRecords A .both
          (omegaPrefix play (n + 1))) :
    let state := profiledRawJointGuardedCommonLeftFiniteStateAfter A strategy
      hwin pair (omegaPrefix inputs n)
    let monitor := profiledRawJointGuardedLeftPhysicalSiblingMonitor A
      pair.1.2.1 false
    let controller := (pair.1.2).memberController A false
    let record := narrowedRecord monitor (controller.labelOf state.1) state.2
      (inputs n)
    let play := treePlay
      (narrowedInducedTree monitor controller.labeledTree) inputs
    A.run word
        (start +
          (profiledRawJointTargetLeftPhysicalPrefixRecords A .both
            (omegaPrefix play (n + 1))).length) =
      (pairedLeftScanPairForRow A .both
        (pairedLeftScanStep A state.2.base.2.1
          (profiledRawJointTargetLeftPhysicalLetter A record))).1 := by
  dsimp only at hslice ⊢
  let monitor := profiledRawJointGuardedLeftPhysicalSiblingMonitor A
    pair.1.2.1 false
  let base := profiledRawJointLeftPhysicalSiblingMonitor A
    pair.1.2.1.base false
  let controller := (pair.1.2).memberController A false
  let play := treePlay
    (narrowedInducedTree monitor controller.labeledTree) inputs
  let state := profiledRawJointGuardedCommonLeftFiniteStateAfter A strategy
    hwin pair (omegaPrefix inputs n)
  let record := narrowedRecord monitor (controller.labelOf state.1) state.2
    (inputs n)
  have hrunGuard : monitor.run play n = state.2 := by
    unfold state
    rw [profiledRawJointGuardedCommonLeftFiniteStateAfter_eq A strategy hwin]
    rw [← monitor.lift_control_branchNode
      (narrowedInducedTree monitor controller.labeledTree) inputs,
      lift_control_narrowedInducedTree, branchNode_eq_omegaPrefix]
  have hrunBase : base.run play n = state.2.base := by
    rw [← BlockRecordMonitor.firstLetterGuard_run_base base
      pair.1.2.1.firstAllowed play n]
    exact congrArg (fun guardState ↦ guardState.base) hrunGuard
  have halign :=
    profiledRawJointTargetLeft_run_add_eq_scanCurrent_of_slice A
      (profiledRawJointUnitLeftTargetProjection A)
      (profiledRawJointLeftPhysicalSiblingAllowed A pair.1.2.1.base)
      pair.1.2.1.base.source play (n + 1) .both word start hentry hslice
  change A.run word
      (start +
        (profiledRawJointTargetLeftPhysicalPrefixRecords A .both
          (omegaPrefix play (n + 1))).length) =
    (pairedLeftScanPairForRow A .both
      (pairedLeftScanStep A state.2.base.2.1
        (profiledRawJointTargetLeftPhysicalLetter A record))).1
  rw [BlockRecordMonitor.run, hrunBase] at halign
  change _ = (pairedLeftScanPairForRow A .both
    (pairedLeftScanStep A state.2.base.2.1
      (profiledRawJointTargetLeftPhysicalLetter A (play n)))).1 at halign
  have hat := profiledRawJointGuardedCommonLeftLiteralPlay_at A strategy hwin
    pair inputs n
  change play n = record at hat
  rw [hat] at halign
  exact halign

/-! ## The literal guarded block is the actual mega trace -/

variable
  (controllers : ProfiledRawJointRootCompatibleInitialControllers A strategy)
  (initialBank : ProfiledRawJointInitialControllerBank A strategy)

private abbrev RetainedTag :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A strategy
    hwin

private abbrev Mega (fallbackTag : RetainedTag A strategy hwin) :=
  MegaGuardedLinkedPhysicalController A strategy hwin controllers initialBank
    fallbackTag

/-- An infinite right-block input word as a physical environment. -/
def profiledRawJointHybridMegaGuardedStrictRightEnvironment
    (inputs : Nat → In₂ × In₁) : EnvironmentSequence In₁ In₂ :=
  fun n ↦ ⟨(inputs n).2, (inputs n).1, .right⟩

/-- Initial coupled mega state at a represented guarded installation. -/
noncomputable def profiledRawJointHybridMegaGuardedCoupledControls
    (fallbackTag : RetainedTag A strategy hwin)
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂) :
    (Mega A strategy hwin controllers initialBank fallbackTag).globalMachine.State :=
  ((.exceptional (.inr (.inl
      (initialProfiledRawJointHybridGuardedCoupledOne A strategy hwin
        installation))), oldOutputOne),
    (.exceptional (.inr (.inl
      (initialProfiledRawJointHybridGuardedCoupledTwo A strategy hwin
        installation))), oldOutputTwo))

/-- The canonical right-prefix mega state, with the literal finite-monitor
outputs stored in its Moore output coordinates. -/
noncomputable def profiledRawJointHybridMegaGuardedRightPrefixStateAt
    (fallbackTag : RetainedTag A strategy hwin)
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (inputs : Nat → In₂ × In₁) (n : Nat) :
    (Mega A strategy hwin controllers initialBank fallbackTag).globalMachine.State :=
  let pair := profiledRawJointHybridGuardedCommonPairAt A strategy hwin
    installation
  let state := profiledRawJointGuardedCommonRightFiniteStateAfter A strategy
    hwin pair (omegaPrefix inputs n)
  let monitor := profiledRawJointGuardedRightPhysicalSiblingMonitor A
    pair.1.1.1 false
  let controller := (pair.1.1).memberController A false
  let record := narrowedRecord monitor (controller.labelOf state.1) state.2
    (inputs n)
  let physical := profiledRawJointTargetRightPhysicalLetter A record
  profiledRawJointHybridMegaGuardedLinkedRightPrefixControls A strategy hwin
    controllers initialBank fallbackTag installation (omegaPrefix inputs n)
      (inputs n) physical.2.2
        (pairedRightInformedForRow .both physical.2.1)

/-- On an all-right continuation, the rerooted mega front follows the exact
guarded finite-prefix state after every positive number of rounds. -/
theorem profiledRawJointHybridMegaGuarded_rightPrefix_globalStateTrace
    (fallbackTag : RetainedTag A strategy hwin)
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (inputs : Nat → In₂ × In₁) : ∀ n : Nat,
    ((Mega A strategy hwin controllers initialBank fallbackTag).globalMachine
        |>.reroot
          (profiledRawJointHybridMegaGuardedCoupledControls A strategy hwin
            controllers initialBank fallbackTag installation oldOutputOne
              oldOutputTwo)).globalStateTrace
        (profiledRawJointHybridMegaGuardedStrictRightEnvironment inputs)
        (n + 1) =
      profiledRawJointHybridMegaGuardedRightPrefixStateAt A strategy hwin
        controllers initialBank fallbackTag installation inputs n := by
  intro n
  induction n with
  | zero =>
      rw [FiniteGlobalRoundMachine.globalStateTrace_succ]
      change
        (Mega A strategy hwin controllers initialBank fallbackTag).advanceControls
            (profiledRawJointHybridMegaGuardedCoupledControls A strategy hwin
              controllers initialBank fallbackTag installation oldOutputOne
                oldOutputTwo)
            ⟨(inputs 0).2, (inputs 0).1, .right⟩ = _
      unfold profiledRawJointHybridMegaGuardedCoupledControls
      unfold profiledRawJointHybridMegaGuardedRightPrefixStateAt
      rw [profiledRawJointHybridMegaGuardedLinked_coupled_right_prefix A
        strategy hwin controllers initialBank]
      cases installation <;> rfl
  | succ n ih =>
      rw [FiniteGlobalRoundMachine.globalStateTrace_succ, ih]
      rw [FiniteGlobalRoundMachine.reroot_step]
      change
        (Mega A strategy hwin controllers initialBank fallbackTag).advanceControls
            (profiledRawJointHybridMegaGuardedRightPrefixStateAt A strategy
              hwin controllers initialBank fallbackTag installation inputs n)
            ⟨(inputs (n + 1)).2, (inputs (n + 1)).1, .right⟩ = _
      unfold profiledRawJointHybridMegaGuardedRightPrefixStateAt
      rw [profiledRawJointHybridMegaGuardedLinked_rightPrefix_right A strategy
        hwin controllers initialBank]
      rw [omegaPrefix_succ]
      generalize hnext : inputs (n + 1) = nextInput
      rcases nextInput with ⟨nextInputTwo, nextInputOne⟩
      rw [profiledRawJointHybridGuardedRightPrefixOwner_step_output A
        strategy hwin installation]
      rw [profiledRawJointHybridGuardedRightPrefixReceiverAfter_step_output A
        strategy hwin installation]

/-- Literal guarded-right controller play selected by an installation. -/
noncomputable def profiledRawJointHybridMegaGuardedRightLiteralPlay
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (inputs : Nat → In₂ × In₁) :=
  let pair := profiledRawJointHybridGuardedCommonPairAt A strategy hwin
    installation
  let monitor := profiledRawJointGuardedRightPhysicalSiblingMonitor A
    pair.1.1.1 false
  let controller := (pair.1.1).memberController A false
  treePlay (narrowedInducedTree monitor controller.labeledTree) inputs

/-- The all-right mega word from a coupled installation is pointwise exactly
the `.both` physical projection of that literal guarded play. -/
theorem profiledRawJointHybridMegaGuarded_rightPrefix_traceWord_apply
    (fallbackTag : RetainedTag A strategy hwin)
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (inputs : Nat → In₂ × In₁) (n : Nat) :
    let mega := Mega A strategy hwin controllers initialBank fallbackTag
    let entry := profiledRawJointHybridMegaGuardedCoupledControls A strategy
      hwin controllers initialBank fallbackTag installation oldOutputOne
        oldOutputTwo
    let env := profiledRawJointHybridMegaGuardedStrictRightEnvironment inputs
    let play := profiledRawJointHybridMegaGuardedRightLiteralPlay A strategy
      hwin installation inputs
    (mega.globalMachine.reroot entry).globalMachineTraceWord
        mega.globalOutputOne mega.globalOutputTwo env n =
      pairedRightRecordForRow .both
        (profiledRawJointTargetRightPhysicalLetter A (play n)) := by
  dsimp only
  rw [FiniteGlobalRoundMachine.globalMachineTraceWord]
  rw [profiledRawJointHybridMegaGuarded_rightPrefix_globalStateTrace A
    strategy hwin controllers initialBank fallbackTag installation
      oldOutputOne oldOutputTwo inputs n]
  let pair := profiledRawJointHybridGuardedCommonPairAt A strategy hwin
    installation
  let state := profiledRawJointGuardedCommonRightFiniteStateAfter A strategy
    hwin pair (omegaPrefix inputs n)
  let monitor := profiledRawJointGuardedRightPhysicalSiblingMonitor A
    pair.1.1.1 false
  let controller := (pair.1.1).memberController A false
  let record := narrowedRecord monitor (controller.labelOf state.1) state.2
    (inputs n)
  let play := profiledRawJointHybridMegaGuardedRightLiteralPlay A strategy hwin
    installation inputs
  have hat :=
    profiledRawJointGuardedCommonRightLiteralPlay_at A strategy hwin pair
      inputs n
  change play n = record at hat
  change _ = pairedRightRecordForRow .both
    (profiledRawJointTargetRightPhysicalLetter A (play n))
  rw [hat]
  unfold profiledRawJointHybridMegaGuardedStrictRightEnvironment
  unfold profiledRawJointHybridMegaGuardedRightPrefixStateAt
  rfl

/-- Whole-word form of the literal guarded-right trace identification. -/
theorem profiledRawJointHybridMegaGuarded_rightPrefix_traceWord_eq
    (fallbackTag : RetainedTag A strategy hwin)
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (inputs : Nat → In₂ × In₁) :
    let mega := Mega A strategy hwin controllers initialBank fallbackTag
    let entry := profiledRawJointHybridMegaGuardedCoupledControls A strategy
      hwin controllers initialBank fallbackTag installation oldOutputOne
        oldOutputTwo
    let env := profiledRawJointHybridMegaGuardedStrictRightEnvironment inputs
    let play := profiledRawJointHybridMegaGuardedRightLiteralPlay A strategy
      hwin installation inputs
    (mega.globalMachine.reroot entry).globalMachineTraceWord
        mega.globalOutputOne mega.globalOutputTwo env =
      fun n ↦ pairedRightRecordForRow .both
        (profiledRawJointTargetRightPhysicalLetter A (play n)) := by
  funext n
  exact profiledRawJointHybridMegaGuarded_rightPrefix_traceWord_apply A
    strategy hwin controllers initialBank fallbackTag installation oldOutputOne
      oldOutputTwo inputs n

/-- Every finite prefix of that mega word is the generic target-monitor
physical-prefix list consumed by the exact scan-state theorem. -/
theorem profiledRawJointHybridMegaGuarded_rightPrefix_omegaPrefix_eq
    (fallbackTag : RetainedTag A strategy hwin)
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (inputs : Nat → In₂ × In₁) : ∀ n : Nat,
    let mega := Mega A strategy hwin controllers initialBank fallbackTag
    let entry := profiledRawJointHybridMegaGuardedCoupledControls A strategy
      hwin controllers initialBank fallbackTag installation oldOutputOne
        oldOutputTwo
    let env := profiledRawJointHybridMegaGuardedStrictRightEnvironment inputs
    let play := profiledRawJointHybridMegaGuardedRightLiteralPlay A strategy
      hwin installation inputs
    omegaPrefix
        ((mega.globalMachine.reroot entry).globalMachineTraceWord
          mega.globalOutputOne mega.globalOutputTwo env) n =
      profiledRawJointTargetRightPhysicalPrefixRecords A .both
        (omegaPrefix play n) := by
  intro n
  dsimp only
  rw [profiledRawJointHybridMegaGuarded_rightPrefix_traceWord_eq A strategy
    hwin controllers initialBank fallbackTag installation oldOutputOne
      oldOutputTwo inputs]
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [omegaPrefix_succ, omegaPrefix_succ, ih]
      simp [profiledRawJointTargetRightPhysicalPrefixRecords]

/-- At an actual reached coupled cut, any finite physically-right prefix is
the same literal target-monitor slice.  Rounds after the prefix are replaced
by an all-right completion only in the proof, using finite-state causality. -/
theorem profiledRawJointHybridMegaGuarded_actualRightPrefix_omegaPrefix_eq
    (fallbackTag : RetainedTag A strategy hwin)
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (env : EnvironmentSequence In₁ In₂) (start n : Nat)
    (hphysical :
      (Mega A strategy hwin controllers initialBank fallbackTag).globalMachine.globalStateTrace
          env start =
        profiledRawJointHybridMegaGuardedCoupledControls A strategy hwin
          controllers initialBank fallbackTag installation oldOutputOne
            oldOutputTwo)
    (hright : ∀ k : Nat, k < n → (env (start + k)).graph = .right) :
    let mega := Mega A strategy hwin controllers initialBank fallbackTag
    let inputs : Nat → In₂ × In₁ := fun k ↦
      ((env (start + k)).inputTwo, (env (start + k)).inputOne)
    let play := profiledRawJointHybridMegaGuardedRightLiteralPlay A strategy
      hwin installation inputs
    omegaPrefix
        (OmegaWord.drop
          (mega.globalMachine.globalMachineTraceWord mega.globalOutputOne
            mega.globalOutputTwo env) start) n =
      profiledRawJointTargetRightPhysicalPrefixRecords A .both
        (omegaPrefix play n) := by
  dsimp only
  let mega := Mega A strategy hwin controllers initialBank fallbackTag
  let G := mega.globalMachine
  let entry := profiledRawJointHybridMegaGuardedCoupledControls A strategy hwin
    controllers initialBank fallbackTag installation oldOutputOne oldOutputTwo
  let inputs : Nat → In₂ × In₁ := fun k ↦
    ((env (start + k)).inputTwo, (env (start + k)).inputOne)
  let rightEnv := profiledRawJointHybridMegaGuardedStrictRightEnvironment
    inputs
  have hreroot := G.reroot_globalMachineTraceWord_drop mega.globalOutputOne
    mega.globalOutputTwo env start
  change G.globalStateTrace env start = entry at hphysical
  rw [hphysical] at hreroot
  have hcausal :=
    (G.reroot entry).omegaPrefix_globalMachineTraceWord_eq_of_forall_lt
      mega.globalOutputOne mega.globalOutputTwo (OmegaWord.drop env start)
        rightEnv n (by
          intro k hk
          have hg := hright k hk
          cases hround : env (start + k) with
          | mk inputOne inputTwo graph =>
              rw [hround] at hg
              change graph = .right at hg
              subst graph
              simp [OmegaWord.drop, rightEnv,
                profiledRawJointHybridMegaGuardedStrictRightEnvironment,
                inputs, hround])
  calc
    omegaPrefix
        (OmegaWord.drop
          (G.globalMachineTraceWord mega.globalOutputOne mega.globalOutputTwo
            env) start) n =
        omegaPrefix
          ((G.reroot entry).globalMachineTraceWord mega.globalOutputOne
            mega.globalOutputTwo (OmegaWord.drop env start)) n := by
      rw [hreroot]
    _ = omegaPrefix
          ((G.reroot entry).globalMachineTraceWord mega.globalOutputOne
            mega.globalOutputTwo rightEnv) n := hcausal
    _ = profiledRawJointTargetRightPhysicalPrefixRecords A .both
          (omegaPrefix
            (profiledRawJointHybridMegaGuardedRightLiteralPlay A strategy hwin
              installation inputs) n) :=
      profiledRawJointHybridMegaGuarded_rightPrefix_omegaPrefix_eq A strategy
        hwin controllers initialBank fallbackTag installation oldOutputOne
          oldOutputTwo inputs n

/-- Exact actual mega control after a nonempty finite right prefix from a
reached coupled installation. -/
theorem profiledRawJointHybridMegaGuarded_actualRightPrefix_globalStateTrace
    (fallbackTag : RetainedTag A strategy hwin)
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (env : EnvironmentSequence In₁ In₂) (start n : Nat)
    (hphysical :
      (Mega A strategy hwin controllers initialBank fallbackTag).globalMachine.globalStateTrace
          env start =
        profiledRawJointHybridMegaGuardedCoupledControls A strategy hwin
          controllers initialBank fallbackTag installation oldOutputOne
            oldOutputTwo)
    (hright : ∀ k : Nat, k < n + 1 →
      (env (start + k)).graph = .right) :
    let inputs : Nat → In₂ × In₁ := fun k ↦
      ((env (start + k)).inputTwo, (env (start + k)).inputOne)
    (Mega A strategy hwin controllers initialBank fallbackTag).globalMachine.globalStateTrace
        env (start + (n + 1)) =
      profiledRawJointHybridMegaGuardedRightPrefixStateAt A strategy hwin
        controllers initialBank fallbackTag installation inputs n := by
  dsimp only
  let mega := Mega A strategy hwin controllers initialBank fallbackTag
  let G := mega.globalMachine
  let entry := profiledRawJointHybridMegaGuardedCoupledControls A strategy hwin
    controllers initialBank fallbackTag installation oldOutputOne oldOutputTwo
  let inputs : Nat → In₂ × In₁ := fun k ↦
    ((env (start + k)).inputTwo, (env (start + k)).inputOne)
  let rightEnv := profiledRawJointHybridMegaGuardedStrictRightEnvironment
    inputs
  change G.globalStateTrace env start = entry at hphysical
  have hdrop := G.reroot_globalStateTrace_drop env start (n + 1)
  rw [hphysical] at hdrop
  have hcausal :
      (G.reroot entry).globalStateTrace (OmegaWord.drop env start) (n + 1) =
        (G.reroot entry).globalStateTrace rightEnv (n + 1) := by
    apply (G.reroot entry).globalStateTrace_eq_of_forall_lt
    intro k hk
    have hg := hright k hk
    cases hround : env (start + k) with
    | mk inputOne inputTwo graph =>
        rw [hround] at hg
        change graph = .right at hg
        subst graph
        simp [OmegaWord.drop, rightEnv,
          profiledRawJointHybridMegaGuardedStrictRightEnvironment, inputs,
          hround]
  have htraj :
      (G.reroot entry).globalStateTrace rightEnv (n + 1) =
        profiledRawJointHybridMegaGuardedRightPrefixStateAt A strategy hwin
          controllers initialBank fallbackTag installation inputs n := by
    simpa [G, mega, entry, rightEnv] using
      (profiledRawJointHybridMegaGuarded_rightPrefix_globalStateTrace A
        strategy hwin controllers initialBank fallbackTag installation
          oldOutputOne oldOutputTwo inputs n)
  exact Eq.trans (Eq.symm hdrop) (Eq.trans hcausal htraj)

/-- The actual checker at the same right-prefix endpoint is the finite
guarded scan current. -/
theorem profiledRawJointHybridMegaGuarded_actualRightPrefix_run_eq_scanCurrent
    (fallbackTag : RetainedTag A strategy hwin)
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (env : EnvironmentSequence In₁ In₂) (start n : Nat)
    (hphysical :
      (Mega A strategy hwin controllers initialBank fallbackTag).globalMachine.globalStateTrace
          env start =
        profiledRawJointHybridMegaGuardedCoupledControls A strategy hwin
          controllers initialBank fallbackTag installation oldOutputOne
            oldOutputTwo)
    (hentry :
      let pair := profiledRawJointHybridGuardedCommonPairAt A strategy hwin
        installation
      let mega := Mega A strategy hwin controllers initialBank fallbackTag
      A.run
          (mega.globalMachine.globalMachineTraceWord mega.globalOutputOne
            mega.globalOutputTwo env) start =
        pairedCodeStateForRow A .both pair.1.1.1.base.source.1.1)
    (hright : ∀ k : Nat, k < n + 1 →
      (env (start + k)).graph = .right) :
    let pair := profiledRawJointHybridGuardedCommonPairAt A strategy hwin
      installation
    let inputs : Nat → In₂ × In₁ := fun k ↦
      ((env (start + k)).inputTwo, (env (start + k)).inputOne)
    let state := profiledRawJointGuardedCommonRightFiniteStateAfter A strategy
      hwin pair (omegaPrefix inputs n)
    let monitor := profiledRawJointGuardedRightPhysicalSiblingMonitor A
      pair.1.1.1 false
    let controller := (pair.1.1).memberController A false
    let record := narrowedRecord monitor (controller.labelOf state.1) state.2
      (inputs n)
    let mega := Mega A strategy hwin controllers initialBank fallbackTag
    A.run
        (mega.globalMachine.globalMachineTraceWord mega.globalOutputOne
          mega.globalOutputTwo env) (start + (n + 1)) =
      (pairedRightScanPairForRow A .both
        (pairedRightScanStep A state.2.base.2.1
          (profiledRawJointTargetRightPhysicalLetter A record))).1 := by
  dsimp only at hentry ⊢
  let pair := profiledRawJointHybridGuardedCommonPairAt A strategy hwin
    installation
  let mega := Mega A strategy hwin controllers initialBank fallbackTag
  let word := mega.globalMachine.globalMachineTraceWord mega.globalOutputOne
    mega.globalOutputTwo env
  let inputs : Nat → In₂ × In₁ := fun k ↦
    ((env (start + k)).inputTwo, (env (start + k)).inputOne)
  have hslice :=
    profiledRawJointHybridMegaGuarded_actualRightPrefix_omegaPrefix_eq A
      strategy hwin controllers initialBank fallbackTag installation
        oldOutputOne oldOutputTwo env start (n + 1) hphysical hright
  have hslice' :
      let monitor := profiledRawJointGuardedRightPhysicalSiblingMonitor A
        pair.1.1.1 false
      let controller := (pair.1.1).memberController A false
      let play := treePlay
        (narrowedInducedTree monitor controller.labeledTree) inputs
      omegaPrefix (OmegaWord.drop word start)
          (profiledRawJointTargetRightPhysicalPrefixRecords A .both
            (omegaPrefix play (n + 1))).length =
        profiledRawJointTargetRightPhysicalPrefixRecords A .both
          (omegaPrefix play (n + 1)) := by
    simpa [word, omegaPrefix,
      profiledRawJointTargetRightPhysicalPrefixRecords] using hslice
  have hscan :=
    profiledRawJointGuardedCommonRight_run_add_eq_scanCurrent_at A strategy
      hwin pair inputs n word start hentry hslice'
  simpa [word, omegaPrefix,
    profiledRawJointTargetRightPhysicalPrefixRecords] using hscan

/-! ## Left-oriented mirror -/

/-- An infinite left-block input word as a physical environment. -/
def profiledRawJointHybridMegaGuardedStrictLeftEnvironment
    (inputs : Nat → In₁ × In₂) : EnvironmentSequence In₁ In₂ :=
  fun n ↦ ⟨(inputs n).1, (inputs n).2, .left⟩

/-- Canonical left-prefix mega state with the literal finite-monitor outputs
stored in its Moore output coordinates. -/
noncomputable def profiledRawJointHybridMegaGuardedLeftPrefixStateAt
    (fallbackTag : RetainedTag A strategy hwin)
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (inputs : Nat → In₁ × In₂) (n : Nat) :
    (Mega A strategy hwin controllers initialBank fallbackTag).globalMachine.State :=
  let pair := profiledRawJointHybridGuardedCommonPairAt A strategy hwin
    installation
  let state := profiledRawJointGuardedCommonLeftFiniteStateAfter A strategy
    hwin pair (omegaPrefix inputs n)
  let monitor := profiledRawJointGuardedLeftPhysicalSiblingMonitor A
    pair.1.2.1 false
  let controller := (pair.1.2).memberController A false
  let record := narrowedRecord monitor (controller.labelOf state.1) state.2
    (inputs n)
  let physical := profiledRawJointTargetLeftPhysicalLetter A record
  profiledRawJointHybridMegaGuardedLinkedLeftPrefixControls A strategy hwin
    controllers initialBank fallbackTag installation (omegaPrefix inputs n)
      (inputs n) (pairedLeftInformedForRow .both physical.2.1) physical.2.2

/-- On an all-left continuation, the rerooted mega front follows the exact
guarded finite-prefix state after every positive number of rounds. -/
theorem profiledRawJointHybridMegaGuarded_leftPrefix_globalStateTrace
    (fallbackTag : RetainedTag A strategy hwin)
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (inputs : Nat → In₁ × In₂) : ∀ n : Nat,
    ((Mega A strategy hwin controllers initialBank fallbackTag).globalMachine
        |>.reroot
          (profiledRawJointHybridMegaGuardedCoupledControls A strategy hwin
            controllers initialBank fallbackTag installation oldOutputOne
              oldOutputTwo)).globalStateTrace
        (profiledRawJointHybridMegaGuardedStrictLeftEnvironment inputs)
        (n + 1) =
      profiledRawJointHybridMegaGuardedLeftPrefixStateAt A strategy hwin
        controllers initialBank fallbackTag installation inputs n := by
  intro n
  induction n with
  | zero =>
      rw [FiniteGlobalRoundMachine.globalStateTrace_succ]
      change
        (Mega A strategy hwin controllers initialBank fallbackTag).advanceControls
            (profiledRawJointHybridMegaGuardedCoupledControls A strategy hwin
              controllers initialBank fallbackTag installation oldOutputOne
                oldOutputTwo)
            ⟨(inputs 0).1, (inputs 0).2, .left⟩ = _
      unfold profiledRawJointHybridMegaGuardedCoupledControls
      unfold profiledRawJointHybridMegaGuardedLeftPrefixStateAt
      rw [profiledRawJointHybridMegaGuardedLinked_coupled_left_prefix A
        strategy hwin controllers initialBank]
      cases installation <;> rfl
  | succ n ih =>
      rw [FiniteGlobalRoundMachine.globalStateTrace_succ, ih]
      rw [FiniteGlobalRoundMachine.reroot_step]
      change
        (Mega A strategy hwin controllers initialBank fallbackTag).advanceControls
            (profiledRawJointHybridMegaGuardedLeftPrefixStateAt A strategy
              hwin controllers initialBank fallbackTag installation inputs n)
            ⟨(inputs (n + 1)).1, (inputs (n + 1)).2, .left⟩ = _
      unfold profiledRawJointHybridMegaGuardedLeftPrefixStateAt
      rw [profiledRawJointHybridMegaGuardedLinked_leftPrefix_left A strategy
        hwin controllers initialBank]
      rw [omegaPrefix_succ]
      generalize hnext : inputs (n + 1) = nextInput
      rcases nextInput with ⟨nextInputOne, nextInputTwo⟩
      rw [profiledRawJointHybridGuardedLeftPrefixReceiverAfter_step_output A
        strategy hwin installation]
      rw [profiledRawJointHybridGuardedLeftPrefixOwner_step_output A strategy
        hwin installation]

/-- Literal guarded-left controller play selected by an installation. -/
noncomputable def profiledRawJointHybridMegaGuardedLeftLiteralPlay
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (inputs : Nat → In₁ × In₂) :=
  let pair := profiledRawJointHybridGuardedCommonPairAt A strategy hwin
    installation
  let monitor := profiledRawJointGuardedLeftPhysicalSiblingMonitor A
    pair.1.2.1 false
  let controller := (pair.1.2).memberController A false
  treePlay (narrowedInducedTree monitor controller.labeledTree) inputs

/-- The all-left mega word from a coupled installation is pointwise exactly
the `.both` physical projection of that literal guarded play. -/
theorem profiledRawJointHybridMegaGuarded_leftPrefix_traceWord_apply
    (fallbackTag : RetainedTag A strategy hwin)
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (inputs : Nat → In₁ × In₂) (n : Nat) :
    let mega := Mega A strategy hwin controllers initialBank fallbackTag
    let entry := profiledRawJointHybridMegaGuardedCoupledControls A strategy
      hwin controllers initialBank fallbackTag installation oldOutputOne
        oldOutputTwo
    let env := profiledRawJointHybridMegaGuardedStrictLeftEnvironment inputs
    let play := profiledRawJointHybridMegaGuardedLeftLiteralPlay A strategy
      hwin installation inputs
    (mega.globalMachine.reroot entry).globalMachineTraceWord
        mega.globalOutputOne mega.globalOutputTwo env n =
      pairedLeftRecordForRow .both
        (profiledRawJointTargetLeftPhysicalLetter A (play n)) := by
  dsimp only
  rw [FiniteGlobalRoundMachine.globalMachineTraceWord]
  rw [profiledRawJointHybridMegaGuarded_leftPrefix_globalStateTrace A
    strategy hwin controllers initialBank fallbackTag installation
      oldOutputOne oldOutputTwo inputs n]
  let pair := profiledRawJointHybridGuardedCommonPairAt A strategy hwin
    installation
  let state := profiledRawJointGuardedCommonLeftFiniteStateAfter A strategy
    hwin pair (omegaPrefix inputs n)
  let monitor := profiledRawJointGuardedLeftPhysicalSiblingMonitor A
    pair.1.2.1 false
  let controller := (pair.1.2).memberController A false
  let record := narrowedRecord monitor (controller.labelOf state.1) state.2
    (inputs n)
  let play := profiledRawJointHybridMegaGuardedLeftLiteralPlay A strategy hwin
    installation inputs
  have hat :=
    profiledRawJointGuardedCommonLeftLiteralPlay_at A strategy hwin pair
      inputs n
  change play n = record at hat
  change _ = pairedLeftRecordForRow .both
    (profiledRawJointTargetLeftPhysicalLetter A (play n))
  rw [hat]
  unfold profiledRawJointHybridMegaGuardedStrictLeftEnvironment
  unfold profiledRawJointHybridMegaGuardedLeftPrefixStateAt
  rfl

/-- Whole-word form of the literal guarded-left trace identification. -/
theorem profiledRawJointHybridMegaGuarded_leftPrefix_traceWord_eq
    (fallbackTag : RetainedTag A strategy hwin)
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (inputs : Nat → In₁ × In₂) :
    let mega := Mega A strategy hwin controllers initialBank fallbackTag
    let entry := profiledRawJointHybridMegaGuardedCoupledControls A strategy
      hwin controllers initialBank fallbackTag installation oldOutputOne
        oldOutputTwo
    let env := profiledRawJointHybridMegaGuardedStrictLeftEnvironment inputs
    let play := profiledRawJointHybridMegaGuardedLeftLiteralPlay A strategy
      hwin installation inputs
    (mega.globalMachine.reroot entry).globalMachineTraceWord
        mega.globalOutputOne mega.globalOutputTwo env =
      fun n ↦ pairedLeftRecordForRow .both
        (profiledRawJointTargetLeftPhysicalLetter A (play n)) := by
  funext n
  exact profiledRawJointHybridMegaGuarded_leftPrefix_traceWord_apply A
    strategy hwin controllers initialBank fallbackTag installation oldOutputOne
      oldOutputTwo inputs n

/-- Every finite prefix of the left mega word is the generic target-monitor
physical-prefix list consumed by the exact scan-state theorem. -/
theorem profiledRawJointHybridMegaGuarded_leftPrefix_omegaPrefix_eq
    (fallbackTag : RetainedTag A strategy hwin)
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (inputs : Nat → In₁ × In₂) : ∀ n : Nat,
    let mega := Mega A strategy hwin controllers initialBank fallbackTag
    let entry := profiledRawJointHybridMegaGuardedCoupledControls A strategy
      hwin controllers initialBank fallbackTag installation oldOutputOne
        oldOutputTwo
    let env := profiledRawJointHybridMegaGuardedStrictLeftEnvironment inputs
    let play := profiledRawJointHybridMegaGuardedLeftLiteralPlay A strategy
      hwin installation inputs
    omegaPrefix
        ((mega.globalMachine.reroot entry).globalMachineTraceWord
          mega.globalOutputOne mega.globalOutputTwo env) n =
      profiledRawJointTargetLeftPhysicalPrefixRecords A .both
        (omegaPrefix play n) := by
  intro n
  dsimp only
  rw [profiledRawJointHybridMegaGuarded_leftPrefix_traceWord_eq A strategy
    hwin controllers initialBank fallbackTag installation oldOutputOne
      oldOutputTwo inputs]
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [omegaPrefix_succ, omegaPrefix_succ, ih]
      simp [profiledRawJointTargetLeftPhysicalPrefixRecords]

/-- Actual-environment left-prefix slice at a reached coupled cut. -/
theorem profiledRawJointHybridMegaGuarded_actualLeftPrefix_omegaPrefix_eq
    (fallbackTag : RetainedTag A strategy hwin)
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (env : EnvironmentSequence In₁ In₂) (start n : Nat)
    (hphysical :
      (Mega A strategy hwin controllers initialBank fallbackTag).globalMachine.globalStateTrace
          env start =
        profiledRawJointHybridMegaGuardedCoupledControls A strategy hwin
          controllers initialBank fallbackTag installation oldOutputOne
            oldOutputTwo)
    (hleft : ∀ k : Nat, k < n → (env (start + k)).graph = .left) :
    let mega := Mega A strategy hwin controllers initialBank fallbackTag
    let inputs : Nat → In₁ × In₂ := fun k ↦
      ((env (start + k)).inputOne, (env (start + k)).inputTwo)
    let play := profiledRawJointHybridMegaGuardedLeftLiteralPlay A strategy
      hwin installation inputs
    omegaPrefix
        (OmegaWord.drop
          (mega.globalMachine.globalMachineTraceWord mega.globalOutputOne
            mega.globalOutputTwo env) start) n =
      profiledRawJointTargetLeftPhysicalPrefixRecords A .both
        (omegaPrefix play n) := by
  dsimp only
  let mega := Mega A strategy hwin controllers initialBank fallbackTag
  let G := mega.globalMachine
  let entry := profiledRawJointHybridMegaGuardedCoupledControls A strategy hwin
    controllers initialBank fallbackTag installation oldOutputOne oldOutputTwo
  let inputs : Nat → In₁ × In₂ := fun k ↦
    ((env (start + k)).inputOne, (env (start + k)).inputTwo)
  let leftEnv := profiledRawJointHybridMegaGuardedStrictLeftEnvironment inputs
  have hreroot := G.reroot_globalMachineTraceWord_drop mega.globalOutputOne
    mega.globalOutputTwo env start
  change G.globalStateTrace env start = entry at hphysical
  rw [hphysical] at hreroot
  have hcausal :=
    (G.reroot entry).omegaPrefix_globalMachineTraceWord_eq_of_forall_lt
      mega.globalOutputOne mega.globalOutputTwo (OmegaWord.drop env start)
        leftEnv n (by
          intro k hk
          have hg := hleft k hk
          cases hround : env (start + k) with
          | mk inputOne inputTwo graph =>
              rw [hround] at hg
              change graph = .left at hg
              subst graph
              simp [OmegaWord.drop, leftEnv,
                profiledRawJointHybridMegaGuardedStrictLeftEnvironment,
                inputs, hround])
  calc
    omegaPrefix
        (OmegaWord.drop
          (G.globalMachineTraceWord mega.globalOutputOne mega.globalOutputTwo
            env) start) n =
        omegaPrefix
          ((G.reroot entry).globalMachineTraceWord mega.globalOutputOne
            mega.globalOutputTwo (OmegaWord.drop env start)) n := by
      rw [hreroot]
    _ = omegaPrefix
          ((G.reroot entry).globalMachineTraceWord mega.globalOutputOne
            mega.globalOutputTwo leftEnv) n := hcausal
    _ = profiledRawJointTargetLeftPhysicalPrefixRecords A .both
          (omegaPrefix
            (profiledRawJointHybridMegaGuardedLeftLiteralPlay A strategy hwin
              installation inputs) n) :=
      profiledRawJointHybridMegaGuarded_leftPrefix_omegaPrefix_eq A strategy
        hwin controllers initialBank fallbackTag installation oldOutputOne
          oldOutputTwo inputs n

/-- Exact actual mega control after a nonempty finite left prefix. -/
theorem profiledRawJointHybridMegaGuarded_actualLeftPrefix_globalStateTrace
    (fallbackTag : RetainedTag A strategy hwin)
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (env : EnvironmentSequence In₁ In₂) (start n : Nat)
    (hphysical :
      (Mega A strategy hwin controllers initialBank fallbackTag).globalMachine.globalStateTrace
          env start =
        profiledRawJointHybridMegaGuardedCoupledControls A strategy hwin
          controllers initialBank fallbackTag installation oldOutputOne
            oldOutputTwo)
    (hleft : ∀ k : Nat, k < n + 1 →
      (env (start + k)).graph = .left) :
    let inputs : Nat → In₁ × In₂ := fun k ↦
      ((env (start + k)).inputOne, (env (start + k)).inputTwo)
    (Mega A strategy hwin controllers initialBank fallbackTag).globalMachine.globalStateTrace
        env (start + (n + 1)) =
      profiledRawJointHybridMegaGuardedLeftPrefixStateAt A strategy hwin
        controllers initialBank fallbackTag installation inputs n := by
  dsimp only
  let mega := Mega A strategy hwin controllers initialBank fallbackTag
  let G := mega.globalMachine
  let entry := profiledRawJointHybridMegaGuardedCoupledControls A strategy hwin
    controllers initialBank fallbackTag installation oldOutputOne oldOutputTwo
  let inputs : Nat → In₁ × In₂ := fun k ↦
    ((env (start + k)).inputOne, (env (start + k)).inputTwo)
  let leftEnv := profiledRawJointHybridMegaGuardedStrictLeftEnvironment inputs
  change G.globalStateTrace env start = entry at hphysical
  have hdrop := G.reroot_globalStateTrace_drop env start (n + 1)
  rw [hphysical] at hdrop
  have hcausal :
      (G.reroot entry).globalStateTrace (OmegaWord.drop env start) (n + 1) =
        (G.reroot entry).globalStateTrace leftEnv (n + 1) := by
    apply (G.reroot entry).globalStateTrace_eq_of_forall_lt
    intro k hk
    have hg := hleft k hk
    cases hround : env (start + k) with
    | mk inputOne inputTwo graph =>
        rw [hround] at hg
        change graph = .left at hg
        subst graph
        simp [OmegaWord.drop, leftEnv,
          profiledRawJointHybridMegaGuardedStrictLeftEnvironment, inputs,
          hround]
  have htraj :
      (G.reroot entry).globalStateTrace leftEnv (n + 1) =
        profiledRawJointHybridMegaGuardedLeftPrefixStateAt A strategy hwin
          controllers initialBank fallbackTag installation inputs n := by
    simpa [G, mega, entry, leftEnv] using
      (profiledRawJointHybridMegaGuarded_leftPrefix_globalStateTrace A
        strategy hwin controllers initialBank fallbackTag installation
          oldOutputOne oldOutputTwo inputs n)
  exact Eq.trans (Eq.symm hdrop) (Eq.trans hcausal htraj)

/-- Exact checker state at the actual left-prefix endpoint. -/
theorem profiledRawJointHybridMegaGuarded_actualLeftPrefix_run_eq_scanCurrent
    (fallbackTag : RetainedTag A strategy hwin)
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (env : EnvironmentSequence In₁ In₂) (start n : Nat)
    (hphysical :
      (Mega A strategy hwin controllers initialBank fallbackTag).globalMachine.globalStateTrace
          env start =
        profiledRawJointHybridMegaGuardedCoupledControls A strategy hwin
          controllers initialBank fallbackTag installation oldOutputOne
            oldOutputTwo)
    (hentry :
      let pair := profiledRawJointHybridGuardedCommonPairAt A strategy hwin
        installation
      let mega := Mega A strategy hwin controllers initialBank fallbackTag
      A.run
          (mega.globalMachine.globalMachineTraceWord mega.globalOutputOne
            mega.globalOutputTwo env) start =
        pairedCodeStateForRow A .both pair.1.2.1.base.source.1.1)
    (hleft : ∀ k : Nat, k < n + 1 →
      (env (start + k)).graph = .left) :
    let pair := profiledRawJointHybridGuardedCommonPairAt A strategy hwin
      installation
    let inputs : Nat → In₁ × In₂ := fun k ↦
      ((env (start + k)).inputOne, (env (start + k)).inputTwo)
    let state := profiledRawJointGuardedCommonLeftFiniteStateAfter A strategy
      hwin pair (omegaPrefix inputs n)
    let monitor := profiledRawJointGuardedLeftPhysicalSiblingMonitor A
      pair.1.2.1 false
    let controller := (pair.1.2).memberController A false
    let record := narrowedRecord monitor (controller.labelOf state.1) state.2
      (inputs n)
    let mega := Mega A strategy hwin controllers initialBank fallbackTag
    A.run
        (mega.globalMachine.globalMachineTraceWord mega.globalOutputOne
          mega.globalOutputTwo env) (start + (n + 1)) =
      (pairedLeftScanPairForRow A .both
        (pairedLeftScanStep A state.2.base.2.1
          (profiledRawJointTargetLeftPhysicalLetter A record))).1 := by
  dsimp only at hentry ⊢
  let pair := profiledRawJointHybridGuardedCommonPairAt A strategy hwin
    installation
  let mega := Mega A strategy hwin controllers initialBank fallbackTag
  let word := mega.globalMachine.globalMachineTraceWord mega.globalOutputOne
    mega.globalOutputTwo env
  let inputs : Nat → In₁ × In₂ := fun k ↦
    ((env (start + k)).inputOne, (env (start + k)).inputTwo)
  have hslice :=
    profiledRawJointHybridMegaGuarded_actualLeftPrefix_omegaPrefix_eq A
      strategy hwin controllers initialBank fallbackTag installation
        oldOutputOne oldOutputTwo env start (n + 1) hphysical hleft
  have hslice' :
      let monitor := profiledRawJointGuardedLeftPhysicalSiblingMonitor A
        pair.1.2.1 false
      let controller := (pair.1.2).memberController A false
      let play := treePlay
        (narrowedInducedTree monitor controller.labeledTree) inputs
      omegaPrefix (OmegaWord.drop word start)
          (profiledRawJointTargetLeftPhysicalPrefixRecords A .both
            (omegaPrefix play (n + 1))).length =
        profiledRawJointTargetLeftPhysicalPrefixRecords A .both
          (omegaPrefix play (n + 1)) := by
    simpa [word, omegaPrefix,
      profiledRawJointTargetLeftPhysicalPrefixRecords] using hslice
  have hscan :=
    profiledRawJointGuardedCommonLeft_run_add_eq_scanCurrent_at A strategy
      hwin pair inputs n word start hentry hslice'
  simpa [word, omegaPrefix,
    profiledRawJointTargetLeftPhysicalPrefixRecords] using hscan

/-! ## Closing the first reversal from an actual coupled cut -/

/-- From an exactly aligned guarded coupled cut, a nonempty right block and
its first strict-left reversal reduce the complete mega word to the certified
persistent-strict child run.  All finite-prefix and root premises are
discharged internally. -/
theorem
    profiledRawJointHybridMegaGuarded_accepts_of_coupled_rightPrefix_leftClose
    (fallbackTag : RetainedTag A strategy hwin)
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (env : EnvironmentSequence In₁ In₂) (start n : Nat)
    (hphysical :
      (Mega A strategy hwin controllers initialBank fallbackTag).globalMachine.globalStateTrace
          env start =
        profiledRawJointHybridMegaGuardedCoupledControls A strategy hwin
          controllers initialBank fallbackTag installation oldOutputOne
            oldOutputTwo)
    (hentry :
      let pair := profiledRawJointHybridGuardedCommonPairAt A strategy hwin
        installation
      let mega := Mega A strategy hwin controllers initialBank fallbackTag
      A.run
          (mega.globalMachine.globalMachineTraceWord mega.globalOutputOne
            mega.globalOutputTwo env) start =
        pairedCodeStateForRow A .both pair.1.1.1.base.source.1.1)
    (hright : ∀ k : Nat, k < n + 1 →
      (env (start + k)).graph = .right)
    (hclose : (env (start + (n + 1))).graph = .left)
    (hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail
        (OmegaWord.drop env (start + (n + 1))) 0))
    (hnoboth : ∀ k : Nat,
      profiledRawJointPhysicalGraphTail
          (OmegaWord.drop env (start + (n + 1))) 0 k ≠ .both) :
    let mega := Mega A strategy hwin controllers initialBank fallbackTag
    A.Accepts
      (mega.globalMachine.globalMachineTraceWord mega.globalOutputOne
        mega.globalOutputTwo env) := by
  dsimp only at hentry ⊢
  let mega := Mega A strategy hwin controllers initialBank fallbackTag
  let inputs : Nat → In₂ × In₁ := fun k ↦
    ((env (start + k)).inputTwo, (env (start + k)).inputOne)
  let past := omegaPrefix inputs n
  let input := inputs n
  let pair := profiledRawJointHybridGuardedCommonPairAt A strategy hwin
    installation
  let state := profiledRawJointGuardedCommonRightFiniteStateAfter A strategy
    hwin pair past
  let monitor := profiledRawJointGuardedRightPhysicalSiblingMonitor A
    pair.1.1.1 false
  let controller := (pair.1.1).memberController A false
  let record := narrowedRecord monitor (controller.labelOf state.1) state.2
    input
  let physical := profiledRawJointTargetRightPhysicalLetter A record
  let outputOne := physical.2.2
  let outputTwo := pairedRightInformedForRow .both physical.2.1
  have hphysicalEnd :=
    profiledRawJointHybridMegaGuarded_actualRightPrefix_globalStateTrace A
      strategy hwin controllers initialBank fallbackTag installation
        oldOutputOne oldOutputTwo env start n hphysical hright
  change mega.globalMachine.globalStateTrace env (start + (n + 1)) =
      profiledRawJointHybridMegaGuardedLinkedRightPrefixControls A strategy
        hwin controllers initialBank fallbackTag installation past input
          outputOne outputTwo at hphysicalEnd
  have hcheckerEnd :=
    profiledRawJointHybridMegaGuarded_actualRightPrefix_run_eq_scanCurrent A
      strategy hwin controllers initialBank fallbackTag installation
        oldOutputOne oldOutputTwo env start n hphysical hentry hright
  change A.run
      (mega.globalMachine.globalMachineTraceWord mega.globalOutputOne
        mega.globalOutputTwo env) (start + (n + 1)) =
    (pairedRightScanPairForRow A .both
      (pairedRightScanStep A state.2.base.2.1 physical)).1 at hcheckerEnd
  obtain ⟨root, hroot⟩ :=
    exists_profiledRawJointHybridGuardedRightPrefixReceiverAfter_targetRoot A
      strategy hwin initialBank installation past input
  cases hround : env (start + (n + 1)) with
  | mk nextInputOne nextInputTwo graph =>
      rw [hround] at hclose
      change graph = .left at hclose
      subst graph
      apply
        profiledRawJointHybridMegaGuardedLinked_accepts_of_rightPrefix_leftClose_persistentStrict
          A strategy hwin controllers initialBank fallbackTag installation
            past input outputOne outputTwo env (start + (n + 1)) nextInputOne
              nextInputTwo hround hterm hnoboth root hroot hphysicalEnd
                hcheckerEnd

/-- Left-block/right-reversal mirror of the complete coupled-cut closure. -/
theorem
    profiledRawJointHybridMegaGuarded_accepts_of_coupled_leftPrefix_rightClose
    (fallbackTag : RetainedTag A strategy hwin)
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (env : EnvironmentSequence In₁ In₂) (start n : Nat)
    (hphysical :
      (Mega A strategy hwin controllers initialBank fallbackTag).globalMachine.globalStateTrace
          env start =
        profiledRawJointHybridMegaGuardedCoupledControls A strategy hwin
          controllers initialBank fallbackTag installation oldOutputOne
            oldOutputTwo)
    (hentry :
      let pair := profiledRawJointHybridGuardedCommonPairAt A strategy hwin
        installation
      let mega := Mega A strategy hwin controllers initialBank fallbackTag
      A.run
          (mega.globalMachine.globalMachineTraceWord mega.globalOutputOne
            mega.globalOutputTwo env) start =
        pairedCodeStateForRow A .both pair.1.2.1.base.source.1.1)
    (hleft : ∀ k : Nat, k < n + 1 →
      (env (start + k)).graph = .left)
    (hclose : (env (start + (n + 1))).graph = .right)
    (hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail
        (OmegaWord.drop env (start + (n + 1))) 0))
    (hnoboth : ∀ k : Nat,
      profiledRawJointPhysicalGraphTail
          (OmegaWord.drop env (start + (n + 1))) 0 k ≠ .both) :
    let mega := Mega A strategy hwin controllers initialBank fallbackTag
    A.Accepts
      (mega.globalMachine.globalMachineTraceWord mega.globalOutputOne
        mega.globalOutputTwo env) := by
  dsimp only at hentry ⊢
  let mega := Mega A strategy hwin controllers initialBank fallbackTag
  let inputs : Nat → In₁ × In₂ := fun k ↦
    ((env (start + k)).inputOne, (env (start + k)).inputTwo)
  let past := omegaPrefix inputs n
  let input := inputs n
  let pair := profiledRawJointHybridGuardedCommonPairAt A strategy hwin
    installation
  let state := profiledRawJointGuardedCommonLeftFiniteStateAfter A strategy
    hwin pair past
  let monitor := profiledRawJointGuardedLeftPhysicalSiblingMonitor A
    pair.1.2.1 false
  let controller := (pair.1.2).memberController A false
  let record := narrowedRecord monitor (controller.labelOf state.1) state.2
    input
  let physical := profiledRawJointTargetLeftPhysicalLetter A record
  let outputOne := pairedLeftInformedForRow .both physical.2.1
  let outputTwo := physical.2.2
  have hphysicalEnd :=
    profiledRawJointHybridMegaGuarded_actualLeftPrefix_globalStateTrace A
      strategy hwin controllers initialBank fallbackTag installation
        oldOutputOne oldOutputTwo env start n hphysical hleft
  change mega.globalMachine.globalStateTrace env (start + (n + 1)) =
      profiledRawJointHybridMegaGuardedLinkedLeftPrefixControls A strategy
        hwin controllers initialBank fallbackTag installation past input
          outputOne outputTwo at hphysicalEnd
  have hcheckerEnd :=
    profiledRawJointHybridMegaGuarded_actualLeftPrefix_run_eq_scanCurrent A
      strategy hwin controllers initialBank fallbackTag installation
        oldOutputOne oldOutputTwo env start n hphysical hentry hleft
  change A.run
      (mega.globalMachine.globalMachineTraceWord mega.globalOutputOne
        mega.globalOutputTwo env) (start + (n + 1)) =
    (pairedLeftScanPairForRow A .both
      (pairedLeftScanStep A state.2.base.2.1 physical)).1 at hcheckerEnd
  obtain ⟨root, hroot⟩ :=
    exists_profiledRawJointHybridGuardedLeftPrefixReceiverAfter_targetRoot A
      strategy hwin initialBank installation past input
  cases hround : env (start + (n + 1)) with
  | mk nextInputOne nextInputTwo graph =>
      rw [hround] at hclose
      change graph = .right at hclose
      subst graph
      apply
        profiledRawJointHybridMegaGuardedLinked_accepts_of_leftPrefix_rightClose_persistentStrict
          A strategy hwin controllers initialBank fallbackTag installation
            past input outputOne outputTwo env (start + (n + 1)) nextInputOne
              nextInputTwo hround hterm hnoboth root hroot hphysicalEnd
                hcheckerEnd

/-! ## A strict block that never closes -/

/-- If the physical run is already at an exactly aligned guarded coupled
cut and remains strict-right forever, the guarded member-controller theorem
accepts its literal Mega suffix. -/
theorem profiledRawJointHybridMegaGuarded_accepts_of_coupled_allRight
    (fallbackTag : RetainedTag A strategy hwin)
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (env : EnvironmentSequence In₁ In₂) (start : Nat)
    (hphysical :
      (Mega A strategy hwin controllers initialBank fallbackTag
        ).globalMachine.globalStateTrace env start =
        profiledRawJointHybridMegaGuardedCoupledControls A strategy hwin
          controllers initialBank fallbackTag installation oldOutputOne
            oldOutputTwo)
    (hentry :
      let pair := profiledRawJointHybridGuardedCommonPairAt A strategy hwin
        installation
      let mega := Mega A strategy hwin controllers initialBank fallbackTag
      A.run
          (mega.globalMachine.globalMachineTraceWord mega.globalOutputOne
            mega.globalOutputTwo env) start =
        pairedCodeStateForRow A .both pair.1.1.1.base.source.1.1)
    (hright : ∀ k : Nat, (env (start + k)).graph = .right) :
    let mega := Mega A strategy hwin controllers initialBank fallbackTag
    A.Accepts
      (mega.globalMachine.globalMachineTraceWord mega.globalOutputOne
        mega.globalOutputTwo env) := by
  dsimp only at hentry ⊢
  let mega := Mega A strategy hwin controllers initialBank fallbackTag
  let pair := profiledRawJointHybridGuardedCommonPairAt A strategy hwin
    installation
  let inputs : Nat → In₂ × In₁ := fun k ↦
    ((env (start + k)).inputTwo, (env (start + k)).inputOne)
  have henv : OmegaWord.drop env start =
      profiledRawJointHybridMegaGuardedStrictRightEnvironment inputs := by
    funext k
    cases hround : env (start + k) with
    | mk inputOne inputTwo graph =>
        have hg := hright k
        rw [hround] at hg
        change graph = .right at hg
        subst graph
        simp [OmegaWord.drop,
          profiledRawJointHybridMegaGuardedStrictRightEnvironment, inputs,
          hround]
  apply A.accepts_of_rerootedGlobalMachine_acceptsFrom mega.globalMachine
    mega.globalOutputOne mega.globalOutputTwo env start
  rw [hphysical, hentry, henv]
  rw [profiledRawJointHybridMegaGuarded_rightPrefix_traceWord_eq A strategy
    hwin controllers initialBank fallbackTag installation oldOutputOne
      oldOutputTwo inputs]
  have hforever := (pair.1.1).memberController_forever A
  have hword :
      pairedRightOmegaWord
          (profiledRawJointGuardedRightControllerLambda A pair.1.1).blind
          (profiledRawJointGuardedRightControllerLambda A pair.1.1
            ).informedBoth inputs =
        fun n ↦ pairedRightRecordForRow .both
          (profiledRawJointTargetRightPhysicalLetter A
            (profiledRawJointHybridMegaGuardedRightLiteralPlay A strategy hwin
              installation inputs n)) := by
    funext n
    simpa [profiledRawJointHybridMegaGuardedRightLiteralPlay, pair] using
      (profiledRawJointGuardedRightControllerLambda_omegaWord_apply A pair.1.1
        inputs n)
  rw [← hword]
  simpa [pair, pairedCodeStateForRow] using hforever.2 inputs

/-- Strict-left mirror of the never-closing guarded block. -/
theorem profiledRawJointHybridMegaGuarded_accepts_of_coupled_allLeft
    (fallbackTag : RetainedTag A strategy hwin)
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (env : EnvironmentSequence In₁ In₂) (start : Nat)
    (hphysical :
      (Mega A strategy hwin controllers initialBank fallbackTag
        ).globalMachine.globalStateTrace env start =
        profiledRawJointHybridMegaGuardedCoupledControls A strategy hwin
          controllers initialBank fallbackTag installation oldOutputOne
            oldOutputTwo)
    (hentry :
      let pair := profiledRawJointHybridGuardedCommonPairAt A strategy hwin
        installation
      let mega := Mega A strategy hwin controllers initialBank fallbackTag
      A.run
          (mega.globalMachine.globalMachineTraceWord mega.globalOutputOne
            mega.globalOutputTwo env) start =
        pairedCodeStateForRow A .both pair.1.2.1.base.source.1.1)
    (hleft : ∀ k : Nat, (env (start + k)).graph = .left) :
    let mega := Mega A strategy hwin controllers initialBank fallbackTag
    A.Accepts
      (mega.globalMachine.globalMachineTraceWord mega.globalOutputOne
        mega.globalOutputTwo env) := by
  dsimp only at hentry ⊢
  let mega := Mega A strategy hwin controllers initialBank fallbackTag
  let pair := profiledRawJointHybridGuardedCommonPairAt A strategy hwin
    installation
  let inputs : Nat → In₁ × In₂ := fun k ↦
    ((env (start + k)).inputOne, (env (start + k)).inputTwo)
  have henv : OmegaWord.drop env start =
      profiledRawJointHybridMegaGuardedStrictLeftEnvironment inputs := by
    funext k
    cases hround : env (start + k) with
    | mk inputOne inputTwo graph =>
        have hg := hleft k
        rw [hround] at hg
        change graph = .left at hg
        subst graph
        simp [OmegaWord.drop,
          profiledRawJointHybridMegaGuardedStrictLeftEnvironment, inputs,
          hround]
  apply A.accepts_of_rerootedGlobalMachine_acceptsFrom mega.globalMachine
    mega.globalOutputOne mega.globalOutputTwo env start
  rw [hphysical, hentry, henv]
  rw [profiledRawJointHybridMegaGuarded_leftPrefix_traceWord_eq A strategy
    hwin controllers initialBank fallbackTag installation oldOutputOne
      oldOutputTwo inputs]
  have hforever := (pair.1.2).memberController_forever A
  have hword :
      pairedLeftOmegaWord
          (profiledRawJointGuardedLeftControllerLambda A pair.1.2).blind
          (profiledRawJointGuardedLeftControllerLambda A pair.1.2
            ).informedBoth inputs =
        fun n ↦ pairedLeftRecordForRow .both
          (profiledRawJointTargetLeftPhysicalLetter A
            (profiledRawJointHybridMegaGuardedLeftLiteralPlay A strategy hwin
              installation inputs n)) := by
    funext n
    simpa [profiledRawJointHybridMegaGuardedLeftLiteralPlay, pair] using
      (profiledRawJointGuardedLeftControllerLambda_omegaWord_apply A pair.1.2
        inputs n)
  rw [← hword]
  simpa [pair, pairedCodeStateForRow] using hforever.2 inputs

end

end DetParityAutomaton

end DistributedSynthesis
