/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridMegaGuardedInitialCheckerAlignment
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonTailAnchoredCrossOutput

/-!
# First simultaneous alignment after a guarded strict prefix

A checked target emitted at the end of a strict prefix stores the action
profile that the old guarded table must realize on the next round.  The same
slot initializes the freshly selected crossed child policy, whose first
informed output realizes that profile as well.  Thus the mixed physical
handoff produced by the first simultaneous round advances the checker from
the old target's `.first` coordinate to the refreshed target's `.both`
coordinate.
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

/-! ## Fresh unit policies realize their stored root profile -/

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Restarting a left unit policy at `.first` makes its first informed output
equal to the action profile stored in the left macro's slot. -/
theorem profiledRawJointUnitRestartLeft_first_output_eq_slot
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy (initial.code A)
      policy) (input : In₁ × In₂) :
    let restart := profiledRawJointUnitRestartLeft A strategy initial policy
      bank source .first
    let next := continueProfiledRawJointUnitLeftPolicyReceiver A strategy
      initial policy bank restart.2 restart.1 input
    next.1 = source.slot.2 input := by
  classical
  dsimp only
  let monitor := profiledRawJointUnitLeftBlockMonitor.{u, v, x, y, s,
    max u v x y s} A strategy (initial.code A) policy source.state source.slot
  let controller := (bank.left source).1
  let env : Nat → In₁ × In₂ := omegaOfList [input]
  let tree := narrowedInducedTree monitor controller.labeledTree
  let play := treePlay tree env
  have htree : monitor.lift.WinningTree tree :=
    narrowedInducedTree_winningTree_of_allThreadsWin monitor
      (ProfiledRawJointUnitPolicyControllerBank.leftController_wins A bank
        source)
  have hwins : monitor.WinsPlay play :=
    (monitor.lift_winningTree_iff tree).mp htree env
  have hsafe := profiledRawJointUnitLeftBlockMonitor_safe_of_wins A strategy
    (initial.code A) policy source play hwins 1
  rw [BlockRecordMonitor.run] at hsafe
  simp only [profiledRawJointUnitLeftBlockMonitor, Bool.and_eq_true,
    decide_eq_true_eq] at hsafe
  have hroot :
      pairedLeftInformedForRow .first
          (play 0).2.1.physical =
        source.slot.2 (play 0).1 := by
    simpa [BlockRecordMonitor.run] using hsafe.1.1
  have hat := profiledRawJointUnitLeftPolicy_treePlay_at_prefix A strategy
    initial policy bank source [] input
  change play 0 = _ at hat
  rw [hat] at hroot
  simpa [monitor, controller, play, env,
    profiledRawJointUnitRestartLeft,
    initialProfiledRawJointUnitLeftPolicyOwner,
    initialProfiledRawJointUnitLeftPolicyReceiver,
    continueProfiledRawJointUnitLeftPolicyReceiver,
    profiledRawJointUnitLeftPolicyOwnerControlFor,
    profiledRawJointUnitLeftPhysicalLetter,
    narrowedRecord] using hroot

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Right-unit mirror of the fresh root-output equation. -/
theorem profiledRawJointUnitRestartRight_first_output_eq_slot
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy (initial.code A)
      policy) (input : In₂ × In₁) :
    let restart := profiledRawJointUnitRestartRight A strategy initial policy
      bank source .first
    let next := continueProfiledRawJointUnitRightPolicyReceiver A strategy
      initial policy bank restart.2 restart.1 input
    next.1 = source.slot.2 input := by
  classical
  dsimp only
  let monitor := profiledRawJointUnitRightBlockMonitor.{u, v, x, y, s,
    max u v x y s} A strategy (initial.code A) policy source.state source.slot
  let controller := (bank.right source).1
  let env : Nat → In₂ × In₁ := omegaOfList [input]
  let tree := narrowedInducedTree monitor controller.labeledTree
  let play := treePlay tree env
  have htree : monitor.lift.WinningTree tree :=
    narrowedInducedTree_winningTree_of_allThreadsWin monitor
      (ProfiledRawJointUnitPolicyControllerBank.rightController_wins A bank
        source)
  have hwins : monitor.WinsPlay play :=
    (monitor.lift_winningTree_iff tree).mp htree env
  have hsafe := profiledRawJointUnitRightBlockMonitor_safe_of_wins A strategy
    (initial.code A) policy source play hwins 1
  rw [BlockRecordMonitor.run] at hsafe
  simp only [profiledRawJointUnitRightBlockMonitor, Bool.and_eq_true,
    decide_eq_true_eq] at hsafe
  have hroot :
      pairedRightInformedForRow .first
          (play 0).2.1.physical =
        source.slot.2 (play 0).1 := by
    simpa [BlockRecordMonitor.run] using hsafe.1.1
  have hat := profiledRawJointUnitRightPolicy_treePlay_at_prefix A strategy
    initial policy bank source [] input
  change play 0 = _ at hat
  rw [hat] at hroot
  simpa [monitor, controller, play, env,
    profiledRawJointUnitRestartRight,
    initialProfiledRawJointUnitRightPolicyOwner,
    initialProfiledRawJointUnitRightPolicyReceiver,
    continueProfiledRawJointUnitRightPolicyReceiver,
    profiledRawJointUnitRightPolicyOwnerControlFor,
    profiledRawJointUnitRightPhysicalLetter,
    narrowedRecord] using hroot

/-! ## The old guarded controller realizes the target's live slot -/

variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))
  (initialBank : ProfiledRawJointInitialControllerBank A strategy)

/-- If the last target of a guarded-right strict prefix is staged as
`oldRoot`, then the next guarded-right letter realizes the left action
profile stored in that root. -/
theorem
    profiledRawJointHybridMegaGuarded_rightPrefix_nextClosing_eq_oldRootSlot
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (past : List (In₂ × In₁)) (input nextInput : In₂ × In₁)
    (oldRoot : ProfiledRawJointHybridMegaGuardedRightTargetRoot A strategy hwin
      initialBank)
    (hroot :
      profiledRawJointHybridGuardedRightReceiverTargetRoot? A strategy hwin
          initialBank
          (profiledRawJointHybridGuardedRightPrefixReceiverAfter A strategy
            hwin installation past input) = some oldRoot) :
    let pair := profiledRawJointHybridGuardedCommonPairAt A strategy hwin
      installation
    let state := profiledRawJointGuardedCommonRightFiniteStateAfter A strategy
      hwin pair (past ++ [input])
    let monitor := profiledRawJointGuardedRightPhysicalSiblingMonitor A
      pair.1.1.1 false
    let controller := (pair.1.1).memberController A false
    let record := narrowedRecord monitor (controller.labelOf state.1) state.2
      nextInput
    pairedRightClosingForRow .both
        (profiledRawJointTargetRightPhysicalLetter A record).2.1 =
      oldRoot.2.slot.2 (nextInput.2, nextInput.1) := by
  classical
  dsimp only
  let pair := profiledRawJointHybridGuardedCommonPairAt A strategy hwin
    installation
  let extended := past ++ [input]
  let state := profiledRawJointGuardedCommonRightFiniteStateAfter A strategy
    hwin pair extended
  let base := profiledRawJointRightPhysicalSiblingMonitor A pair.1.1.1.base
    false
  let monitor := profiledRawJointGuardedRightPhysicalSiblingMonitor A
    pair.1.1.1 false
  let controller := (pair.1.1).memberController A false
  let env : Nat → In₂ × In₁ := omegaOfList (extended ++ [nextInput])
  let play := treePlay
    (narrowedInducedTree monitor controller.labeledTree) env
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
      initialBank installation target oldRoot hrootTarget
  have hmonitor :=
    profiledRawJointGuardedCommonRightFiniteStateAfter_monitorRun A strategy
      hwin pair extended nextInput
  change monitor.run play extended.length = state.2 at hmonitor
  have hpending :
      (base.run play extended.length).2.2.1 .both =
        some oldRoot.2.slot.2 := by
    rw [← BlockRecordMonitor.firstLetterGuard_run_base base
      pair.1.1.1.firstAllowed play extended.length]
    rw [hmonitor]
    change
      (profiledRawJointGuardedCommonRightFiniteStateAfter A strategy hwin pair
        (past ++ [input])).2.base.2.2.1 .both = some oldRoot.2.slot.2
    rw [profiledRawJointGuardedCommonRightFiniteStateAfter_append_one A
      strategy hwin pair past input]
    change leftProfileOfProfiledState A
      (profiledRawJointUnitRightTargetProjection A target) =
        some oldRoot.2.slot.2
    simp [
      profiledRawJointUnitRightTargetProjection,
      leftProfileOfProfiledState, hslot]
  have hoverlap :=
    ProfiledRawJointGuardedRightPhysicalSiblingMove.memberController_overlap
      A pair.1.1 false env extended.length .both oldRoot.2.slot.2 hpending
  dsimp only at hoverlap
  have hat := profiledRawJointGuardedCommonRightLiteralPlay_at_prefix A
    strategy hwin pair extended nextInput
  change play extended.length = _ at hat
  change
    pairedRightClosingForRow .both
        (profiledRawJointTargetRightPhysicalLetter A
          (play extended.length)).2.1 =
      oldRoot.2.slot.2
        ((play extended.length).1.2, (play extended.length).1.1) at hoverlap
  rw [hat] at hoverlap
  exact hoverlap

/-- Guarded-left mirror of the delayed live-slot equation. -/
theorem
    profiledRawJointHybridMegaGuarded_leftPrefix_nextClosing_eq_oldRootSlot
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (past : List (In₁ × In₂)) (input nextInput : In₁ × In₂)
    (oldRoot : ProfiledRawJointHybridMegaGuardedLeftTargetRoot A strategy hwin
      initialBank)
    (hroot :
      profiledRawJointHybridGuardedLeftReceiverTargetRoot? A strategy hwin
          initialBank
          (profiledRawJointHybridGuardedLeftPrefixReceiverAfter A strategy
            hwin installation past input) = some oldRoot) :
    let pair := profiledRawJointHybridGuardedCommonPairAt A strategy hwin
      installation
    let state := profiledRawJointGuardedCommonLeftFiniteStateAfter A strategy
      hwin pair (past ++ [input])
    let monitor := profiledRawJointGuardedLeftPhysicalSiblingMonitor A
      pair.1.2.1 false
    let controller := (pair.1.2).memberController A false
    let record := narrowedRecord monitor (controller.labelOf state.1) state.2
      nextInput
    pairedLeftClosingForRow .both
        (profiledRawJointTargetLeftPhysicalLetter A record).2.1 =
      oldRoot.2.slot.2 (nextInput.2, nextInput.1) := by
  classical
  dsimp only
  let pair := profiledRawJointHybridGuardedCommonPairAt A strategy hwin
    installation
  let extended := past ++ [input]
  let state := profiledRawJointGuardedCommonLeftFiniteStateAfter A strategy
    hwin pair extended
  let base := profiledRawJointLeftPhysicalSiblingMonitor A pair.1.2.1.base
    false
  let monitor := profiledRawJointGuardedLeftPhysicalSiblingMonitor A
    pair.1.2.1 false
  let controller := (pair.1.2).memberController A false
  let env : Nat → In₁ × In₂ := omegaOfList (extended ++ [nextInput])
  let play := treePlay
    (narrowedInducedTree monitor controller.labeledTree) env
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
      initialBank installation target oldRoot hrootTarget
  have hmonitor :=
    profiledRawJointGuardedCommonLeftFiniteStateAfter_monitorRun A strategy
      hwin pair extended nextInput
  change monitor.run play extended.length = state.2 at hmonitor
  have hpending :
      (base.run play extended.length).2.2.1 .both =
        some oldRoot.2.slot.2 := by
    rw [← BlockRecordMonitor.firstLetterGuard_run_base base
      pair.1.2.1.firstAllowed play extended.length]
    rw [hmonitor]
    change
      (profiledRawJointGuardedCommonLeftFiniteStateAfter A strategy hwin pair
        (past ++ [input])).2.base.2.2.1 .both = some oldRoot.2.slot.2
    rw [profiledRawJointGuardedCommonLeftFiniteStateAfter_append_one A
      strategy hwin pair past input]
    change rightProfileOfProfiledState A
      (profiledRawJointUnitLeftTargetProjection A target) =
        some oldRoot.2.slot.2
    simp [profiledRawJointUnitLeftTargetProjection,
      rightProfileOfProfiledState, hslot]
  have hoverlap :=
    ProfiledRawJointGuardedLeftPhysicalSiblingMove.memberController_overlap
      A pair.1.2 false env extended.length .both oldRoot.2.slot.2 hpending
  dsimp only at hoverlap
  have hat := profiledRawJointGuardedCommonLeftLiteralPlay_at_prefix A
    strategy hwin pair extended nextInput
  change play extended.length = _ at hat
  change
    pairedLeftClosingForRow .both
        (profiledRawJointTargetLeftPhysicalLetter A
          (play extended.length)).2.1 =
      oldRoot.2.slot.2
        ((play extended.length).1.2, (play extended.length).1.1) at hoverlap
  rw [hat] at hoverlap
  exact hoverlap

/-! ## A locally computable but globally incompatible repair candidate -/

/-- On a receive after a strict-right prefix, process one can compute the
refreshed guarded-right root and stage an unconsumed ordinary left receiver at
that root's `.both` row while retaining the old checked close output.  This is
not the production receive map: the same local receive also occurs on a
strict-left reversal, where process two cannot compute this refreshed root. -/
noncomputable def
    profiledRawJointHybridMegaGuardedRightFirstBothRefreshedLeft?
    (state : ProfiledRawJointHybridGuardedRightInstalledReceiver A strategy
      hwin)
    (owner : ProfiledRawJointHybridGuardedRightInstalledOwner A strategy hwin)
    (inputOne : In₁) (inputTwo : In₂) :
    Option (Out₁ ×
      ProfiledRawJointHybridMegaGuardedStartedLeftReceiver A strategy hwin
        initialBank) :=
  match profiledRawJointHybridMegaGuardedRightCloseReceiverOne? A strategy hwin
      initialBank state inputOne inputTwo with
  | none => none
  | some closed =>
      let nextRight := stepProfiledRawJointHybridGuardedRightReceiver A
        strategy hwin state owner inputTwo inputOne
      match profiledRawJointHybridGuardedRightReceiverTargetRoot? A strategy
          hwin initialBank nextRight.2 with
      | none => none
      | some root =>
          let source := profiledRawJointHybridMegaChildSource A strategy hwin
            initialBank root.1
          let policy := profiledRawJointHybridMegaChildPolicy A strategy hwin
            initialBank root.1
          let receiver := initialProfiledRawJointUnitLeftPolicyReceiver A
            strategy source policy root.2 .both
          some (closed.1, ⟨root.1, receiver⟩)

/-- Strict-left/process-two mirror of the incompatible candidate. -/
noncomputable def
    profiledRawJointHybridMegaGuardedLeftFirstBothRefreshedRight?
    (state : ProfiledRawJointHybridGuardedLeftInstalledReceiver A strategy
      hwin)
    (owner : ProfiledRawJointHybridGuardedLeftInstalledOwner A strategy hwin)
    (inputOne : In₁) (inputTwo : In₂) :
    Option (Out₂ ×
      ProfiledRawJointHybridMegaGuardedStartedRightReceiver A strategy hwin
        initialBank) :=
  match profiledRawJointHybridMegaGuardedLeftCloseReceiverTwo? A strategy hwin
      initialBank state inputTwo inputOne with
  | none => none
  | some closed =>
      let nextLeft := stepProfiledRawJointHybridGuardedLeftReceiver A strategy
        hwin state owner inputOne inputTwo
      match profiledRawJointHybridGuardedLeftReceiverTargetRoot? A strategy
          hwin initialBank nextLeft.2 with
      | none => none
      | some root =>
          let source := profiledRawJointHybridMegaChildSource A strategy hwin
            initialBank root.1
          let policy := profiledRawJointHybridMegaChildPolicy A strategy hwin
            initialBank root.1
          let receiver := initialProfiledRawJointUnitRightPolicyReceiver A
            strategy source policy root.2 .both
          some (closed.1, ⟨root.1, receiver⟩)

/-! ## Local refreshed-control equations -/

/-- On the canonical right prefix, the local candidate succeeds, emits the
already proved delayed close, and stages exactly the refreshed root. -/
theorem
    profiledRawJointHybridMegaGuardedRightFirstBothRefreshedLeft?_eq
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (past : List (In₂ × In₁)) (input nextInput : In₂ × In₁)
    (oldRoot : ProfiledRawJointHybridMegaGuardedRightTargetRoot A strategy hwin
      initialBank)
    (holdRoot :
      profiledRawJointHybridGuardedRightReceiverTargetRoot? A strategy hwin
          initialBank
          (profiledRawJointHybridGuardedRightPrefixReceiverAfter A strategy
            hwin installation past input) = some oldRoot)
    (refreshedRoot :
      ProfiledRawJointHybridMegaGuardedRightTargetRoot A strategy hwin
        initialBank)
    (hrefreshedRoot :
      profiledRawJointHybridGuardedRightReceiverTargetRoot? A strategy hwin
          initialBank
          (profiledRawJointHybridGuardedRightPrefixReceiverAfter A strategy
            hwin installation (past ++ [input]) nextInput) =
        some refreshedRoot) :
    let pair := profiledRawJointHybridGuardedCommonPairAt A strategy hwin
      installation
    let state := profiledRawJointGuardedCommonRightFiniteStateAfter A strategy
      hwin pair (past ++ [input])
    let monitor := profiledRawJointGuardedRightPhysicalSiblingMonitor A
      pair.1.1.1 false
    let controller := (pair.1.1).memberController A false
    let record := narrowedRecord monitor (controller.labelOf state.1) state.2
      nextInput
    let source := profiledRawJointHybridMegaChildSource A strategy hwin
      initialBank refreshedRoot.1
    let policy := profiledRawJointHybridMegaChildPolicy A strategy hwin
      initialBank refreshedRoot.1
    profiledRawJointHybridMegaGuardedRightFirstBothRefreshedLeft? A strategy
        hwin initialBank
        (profiledRawJointHybridGuardedRightPrefixReceiverAfter A strategy hwin
          installation past input)
        (profiledRawJointHybridGuardedRightPrefixOwner A strategy hwin
          installation (past ++ [input])) nextInput.2 nextInput.1 =
      some (pairedRightClosingForRow .both
          (profiledRawJointTargetRightPhysicalLetter A record).2.1,
        ⟨refreshedRoot.1,
          initialProfiledRawJointUnitLeftPolicyReceiver A strategy source
            policy refreshedRoot.2 .both⟩) := by
  classical
  dsimp only
  let oldState :=
    profiledRawJointHybridGuardedRightPrefixReceiverAfter A strategy hwin
      installation past input
  let oldOwner := profiledRawJointHybridGuardedRightPrefixOwner A strategy hwin
    installation (past ++ [input])
  have holdClose :=
    profiledRawJointHybridMegaGuardedRightCloseReceiverOne?_some A strategy
      hwin initialBank oldState oldRoot holdRoot nextInput.2 nextInput.1
  have hnext :=
    profiledRawJointHybridGuardedRightPrefixReceiverAfter_step A strategy hwin
      installation past input nextInput
  have hclosing :=
    (profiledRawJointUnitRestartLeft_first_output_eq_slot A strategy
      (profiledRawJointHybridMegaChildSource A strategy hwin initialBank
        oldRoot.1)
      (profiledRawJointHybridMegaChildPolicy A strategy hwin initialBank
        oldRoot.1)
      (profiledRawJointHybridMegaChildControllerBank A strategy hwin
        initialBank oldRoot.1) oldRoot.2
      (nextInput.2, nextInput.1)).trans
        (profiledRawJointHybridMegaGuarded_rightPrefix_nextClosing_eq_oldRootSlot
          A strategy hwin initialBank installation past input nextInput oldRoot
            holdRoot).symm
  unfold profiledRawJointHybridMegaGuardedRightFirstBothRefreshedLeft?
  rw [holdClose]
  dsimp only
  rw [hnext, hrefreshedRoot]
  dsimp only
  rw [hclosing]

/-- Canonical left-prefix mirror: the process-two candidate preserves the old
delayed close while staging the refreshed right root at `.both`. -/
theorem
    profiledRawJointHybridMegaGuardedLeftFirstBothRefreshedRight?_eq
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (past : List (In₁ × In₂)) (input nextInput : In₁ × In₂)
    (oldRoot : ProfiledRawJointHybridMegaGuardedLeftTargetRoot A strategy hwin
      initialBank)
    (holdRoot :
      profiledRawJointHybridGuardedLeftReceiverTargetRoot? A strategy hwin
          initialBank
          (profiledRawJointHybridGuardedLeftPrefixReceiverAfter A strategy
            hwin installation past input) = some oldRoot)
    (refreshedRoot :
      ProfiledRawJointHybridMegaGuardedLeftTargetRoot A strategy hwin
        initialBank)
    (hrefreshedRoot :
      profiledRawJointHybridGuardedLeftReceiverTargetRoot? A strategy hwin
          initialBank
          (profiledRawJointHybridGuardedLeftPrefixReceiverAfter A strategy
            hwin installation (past ++ [input]) nextInput) =
        some refreshedRoot) :
    let pair := profiledRawJointHybridGuardedCommonPairAt A strategy hwin
      installation
    let state := profiledRawJointGuardedCommonLeftFiniteStateAfter A strategy
      hwin pair (past ++ [input])
    let monitor := profiledRawJointGuardedLeftPhysicalSiblingMonitor A
      pair.1.2.1 false
    let controller := (pair.1.2).memberController A false
    let record := narrowedRecord monitor (controller.labelOf state.1) state.2
      nextInput
    let source := profiledRawJointHybridMegaChildSource A strategy hwin
      initialBank refreshedRoot.1
    let policy := profiledRawJointHybridMegaChildPolicy A strategy hwin
      initialBank refreshedRoot.1
    profiledRawJointHybridMegaGuardedLeftFirstBothRefreshedRight? A strategy
        hwin initialBank
        (profiledRawJointHybridGuardedLeftPrefixReceiverAfter A strategy hwin
          installation past input)
        (profiledRawJointHybridGuardedLeftPrefixOwner A strategy hwin
          installation (past ++ [input])) nextInput.1 nextInput.2 =
      some (pairedLeftClosingForRow .both
          (profiledRawJointTargetLeftPhysicalLetter A record).2.1,
        ⟨refreshedRoot.1,
          initialProfiledRawJointUnitRightPolicyReceiver A strategy source
            policy refreshedRoot.2 .both⟩) := by
  classical
  dsimp only
  let oldState :=
    profiledRawJointHybridGuardedLeftPrefixReceiverAfter A strategy hwin
      installation past input
  let oldOwner := profiledRawJointHybridGuardedLeftPrefixOwner A strategy hwin
    installation (past ++ [input])
  have holdClose :=
    profiledRawJointHybridMegaGuardedLeftCloseReceiverTwo?_some A strategy
      hwin initialBank oldState oldRoot holdRoot nextInput.2 nextInput.1
  have hnext :=
    profiledRawJointHybridGuardedLeftPrefixReceiverAfter_step A strategy hwin
      installation past input nextInput
  have hclosing :=
    (profiledRawJointUnitRestartRight_first_output_eq_slot A strategy
      (profiledRawJointHybridMegaChildSource A strategy hwin initialBank
        oldRoot.1)
      (profiledRawJointHybridMegaChildPolicy A strategy hwin initialBank
        oldRoot.1)
      (profiledRawJointHybridMegaChildControllerBank A strategy hwin
        initialBank oldRoot.1) oldRoot.2
      (nextInput.2, nextInput.1)).trans
        (profiledRawJointHybridMegaGuarded_leftPrefix_nextClosing_eq_oldRootSlot
          A strategy hwin initialBank installation past input nextInput oldRoot
            holdRoot).symm
  unfold profiledRawJointHybridMegaGuardedLeftFirstBothRefreshedRight?
  rw [holdClose]
  dsimp only
  rw [hnext, hrefreshedRoot]
  dsimp only
  rw [hclosing]

/-! ## Unconditional first-simultaneous checker refresh -/

/-- After a guarded-right strict prefix, the actual first simultaneous
physical letter advances the old target's `.first` checker coordinate to the
refreshed target's `.both` coordinate. -/
theorem profiledRawJointHybridMegaGuarded_rightPrefix_firstBoth_step_eq_refreshedBoth
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (past : List (In₂ × In₁)) (input nextInput : In₂ × In₁)
    (oldRoot : ProfiledRawJointHybridMegaGuardedRightTargetRoot A strategy hwin
      initialBank)
    (holdRoot :
      profiledRawJointHybridGuardedRightReceiverTargetRoot? A strategy hwin
          initialBank
          (profiledRawJointHybridGuardedRightPrefixReceiverAfter A strategy
            hwin installation past input) = some oldRoot)
    (refreshedRoot :
      ProfiledRawJointHybridMegaGuardedRightTargetRoot A strategy hwin
        initialBank)
    (hrefreshedRoot :
      profiledRawJointHybridGuardedRightReceiverTargetRoot? A strategy hwin
          initialBank
          (profiledRawJointHybridGuardedRightPrefixReceiverAfter A strategy
            hwin installation (past ++ [input]) nextInput) =
        some refreshedRoot) :
    let source := profiledRawJointHybridMegaChildSource A strategy hwin
      initialBank oldRoot.1
    let policy := profiledRawJointHybridMegaChildPolicy A strategy hwin
      initialBank oldRoot.1
    let bank := profiledRawJointHybridMegaChildControllerBank A strategy hwin
      initialBank oldRoot.1
    let restart := profiledRawJointUnitRestartLeft A strategy source policy bank
      oldRoot.2 .first
    let nextLeft := continueProfiledRawJointUnitLeftPolicyReceiver A strategy
      source policy bank restart.2 restart.1 (nextInput.2, nextInput.1)
    let nextRight := stepProfiledRawJointHybridGuardedRightReceiver A strategy
      hwin
      (profiledRawJointHybridGuardedRightPrefixReceiverAfter A strategy hwin
        installation past input)
      (profiledRawJointHybridGuardedRightPrefixOwner A strategy hwin
        installation (past ++ [input])) nextInput.1 nextInput.2
    let pair := profiledRawJointHybridGuardedCommonPairAt A strategy hwin
      installation
    let state := profiledRawJointGuardedCommonRightFiniteStateAfter A strategy
      hwin pair (past ++ [input])
    let monitor := profiledRawJointGuardedRightPhysicalSiblingMonitor A
      pair.1.1.1 false
    let controller := (pair.1.1).memberController A false
    let record := narrowedRecord monitor (controller.labelOf state.1) state.2
      nextInput
    A.step (pairedCodeStateForRow A .first oldRoot.2.slot.1.1)
        (bothRoundRecord
          ((profiledRawJointTargetRightPhysicalLetter A record).1.2,
            (profiledRawJointTargetRightPhysicalLetter A record).1.1)
          nextLeft.1 nextRight.1) =
      pairedCodeStateForRow A .both refreshedRoot.2.slot.1.1 := by
  apply
    profiledRawJointHybridMegaGuarded_rightPrefix_firstBoth_step_eq_refreshedBoth_of_closingOutput
      A strategy hwin initialBank installation past input nextInput oldRoot
        holdRoot refreshedRoot hrefreshedRoot
  dsimp only
  exact
    (profiledRawJointUnitRestartLeft_first_output_eq_slot A strategy
      (profiledRawJointHybridMegaChildSource A strategy hwin initialBank
        oldRoot.1)
      (profiledRawJointHybridMegaChildPolicy A strategy hwin initialBank
        oldRoot.1)
      (profiledRawJointHybridMegaChildControllerBank A strategy hwin
        initialBank oldRoot.1) oldRoot.2
      (nextInput.2, nextInput.1)).trans
        (profiledRawJointHybridMegaGuarded_rightPrefix_nextClosing_eq_oldRootSlot
          A strategy hwin initialBank installation past input nextInput oldRoot
            holdRoot).symm

/-- Guarded-left mirror of the unconditional first simultaneous checker
refresh. -/
theorem profiledRawJointHybridMegaGuarded_leftPrefix_firstBoth_step_eq_refreshedBoth
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (past : List (In₁ × In₂)) (input nextInput : In₁ × In₂)
    (oldRoot : ProfiledRawJointHybridMegaGuardedLeftTargetRoot A strategy hwin
      initialBank)
    (holdRoot :
      profiledRawJointHybridGuardedLeftReceiverTargetRoot? A strategy hwin
          initialBank
          (profiledRawJointHybridGuardedLeftPrefixReceiverAfter A strategy
            hwin installation past input) = some oldRoot)
    (refreshedRoot :
      ProfiledRawJointHybridMegaGuardedLeftTargetRoot A strategy hwin
        initialBank)
    (hrefreshedRoot :
      profiledRawJointHybridGuardedLeftReceiverTargetRoot? A strategy hwin
          initialBank
          (profiledRawJointHybridGuardedLeftPrefixReceiverAfter A strategy
            hwin installation (past ++ [input]) nextInput) =
        some refreshedRoot) :
    let source := profiledRawJointHybridMegaChildSource A strategy hwin
      initialBank oldRoot.1
    let policy := profiledRawJointHybridMegaChildPolicy A strategy hwin
      initialBank oldRoot.1
    let bank := profiledRawJointHybridMegaChildControllerBank A strategy hwin
      initialBank oldRoot.1
    let restart := profiledRawJointUnitRestartRight A strategy source policy
      bank oldRoot.2 .first
    let nextRight := continueProfiledRawJointUnitRightPolicyReceiver A strategy
      source policy bank restart.2 restart.1 (nextInput.2, nextInput.1)
    let nextLeft := stepProfiledRawJointHybridGuardedLeftReceiver A strategy
      hwin
      (profiledRawJointHybridGuardedLeftPrefixReceiverAfter A strategy hwin
        installation past input)
      (profiledRawJointHybridGuardedLeftPrefixOwner A strategy hwin
        installation (past ++ [input])) nextInput.1 nextInput.2
    let pair := profiledRawJointHybridGuardedCommonPairAt A strategy hwin
      installation
    let state := profiledRawJointGuardedCommonLeftFiniteStateAfter A strategy
      hwin pair (past ++ [input])
    let monitor := profiledRawJointGuardedLeftPhysicalSiblingMonitor A
      pair.1.2.1 false
    let controller := (pair.1.2).memberController A false
    let record := narrowedRecord monitor (controller.labelOf state.1) state.2
      nextInput
    A.step (pairedCodeStateForRow A .first oldRoot.2.slot.1.1)
        (bothRoundRecord
          (profiledRawJointTargetLeftPhysicalLetter A record).1
          nextLeft.1 nextRight.1) =
      pairedCodeStateForRow A .both refreshedRoot.2.slot.1.1 := by
  apply
    profiledRawJointHybridMegaGuarded_leftPrefix_firstBoth_step_eq_refreshedBoth_of_closingOutput
      A strategy hwin initialBank installation past input nextInput oldRoot
        holdRoot refreshedRoot hrefreshedRoot
  dsimp only
  exact
    (profiledRawJointUnitRestartRight_first_output_eq_slot A strategy
      (profiledRawJointHybridMegaChildSource A strategy hwin initialBank
        oldRoot.1)
      (profiledRawJointHybridMegaChildPolicy A strategy hwin initialBank
        oldRoot.1)
      (profiledRawJointHybridMegaChildControllerBank A strategy hwin
        initialBank oldRoot.1) oldRoot.2
      (nextInput.2, nextInput.1)).trans
        (profiledRawJointHybridMegaGuarded_leftPrefix_nextClosing_eq_oldRootSlot
          A strategy hwin initialBank installation past input nextInput oldRoot
            holdRoot).symm

/-! ## The refresh as the actual first letter of the rerooted mega word -/

/-- The first letter emitted by the physical mega controller rerooted at a
guarded-right prefix performs the unconditional checker refresh.  This
packages the Moore-timed physical transition and the DPA step in one equation
for an arbitrary environment tail. -/
theorem
    profiledRawJointHybridMegaGuardedLinked_rightPrefix_firstBoth_word_step_eq_refreshedBoth
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
    (tail : EnvironmentSequence In₁ In₂)
    (oldRoot : ProfiledRawJointHybridMegaGuardedRightTargetRoot A strategy hwin
      initialBank)
    (holdRoot :
      profiledRawJointHybridGuardedRightReceiverTargetRoot? A strategy hwin
          initialBank
          (profiledRawJointHybridGuardedRightPrefixReceiverAfter A strategy
            hwin installation past input) = some oldRoot)
    (refreshedRoot :
      ProfiledRawJointHybridMegaGuardedRightTargetRoot A strategy hwin
        initialBank)
    (hrefreshedRoot :
      profiledRawJointHybridGuardedRightReceiverTargetRoot? A strategy hwin
          initialBank
          (profiledRawJointHybridGuardedRightPrefixReceiverAfter A strategy
            hwin installation (past ++ [input])
              (nextInputTwo, nextInputOne)) = some refreshedRoot) :
    let mega := MegaGuardedLinkedPhysicalController A strategy hwin
      controllers initialBank fallbackTag
    let prefixState :=
      profiledRawJointHybridMegaGuardedLinkedRightPrefixControls A strategy
        hwin controllers initialBank fallbackTag installation past input
          oldOutputOne oldOutputTwo
    let env := OmegaWord.prependList
      [⟨nextInputOne, nextInputTwo, .both⟩] tail
    let word := (mega.globalMachine.reroot prefixState).globalMachineTraceWord
      mega.globalOutputOne mega.globalOutputTwo env
    A.step (pairedCodeStateForRow A .first oldRoot.2.slot.1.1) (word 0) =
      pairedCodeStateForRow A .both refreshedRoot.2.slot.1.1 := by
  dsimp only
  let mega := MegaGuardedLinkedPhysicalController A strategy hwin controllers
    initialBank fallbackTag
  let prefixState :=
    profiledRawJointHybridMegaGuardedLinkedRightPrefixControls A strategy hwin
      controllers initialBank fallbackTag installation past input oldOutputOne
        oldOutputTwo
  let round : EnvironmentRound In₁ In₂ :=
    ⟨nextInputOne, nextInputTwo, .both⟩
  let env : EnvironmentSequence In₁ In₂ :=
    OmegaWord.prependList [round] tail
  have hcontrols :=
    profiledRawJointHybridMegaGuardedLinked_rightPrefix_firstBoth_mixed A
      strategy hwin controllers initialBank fallbackTag installation past
        input oldOutputOne oldOutputTwo nextInputOne nextInputTwo oldRoot
          holdRoot
  have hstep :=
    profiledRawJointHybridMegaGuarded_rightPrefix_firstBoth_step_eq_refreshedBoth
      A strategy hwin initialBank installation past input
        (nextInputTwo, nextInputOne) oldRoot holdRoot refreshedRoot
          hrefreshedRoot
  dsimp only at hcontrols hstep
  change A.step (pairedCodeStateForRow A .first oldRoot.2.slot.1.1)
      {
        inputOne := nextInputOne
        inputTwo := nextInputTwo
        graph := .both
        outputOne := mega.globalOutputOne
          ((mega.globalMachine.reroot prefixState).globalStateTrace env 1)
        outputTwo := mega.globalOutputTwo
          ((mega.globalMachine.reroot prefixState).globalStateTrace env 1)
      } = pairedCodeStateForRow A .both refreshedRoot.2.slot.1.1
  rw [show 1 = 0 + 1 by omega,
    FiniteGlobalRoundMachine.globalStateTrace_succ]
  change A.step _
    {
      inputOne := nextInputOne
      inputTwo := nextInputTwo
      graph := .both
      outputOne := mega.globalOutputOne
        (mega.advanceControls prefixState (env 0))
      outputTwo := mega.globalOutputTwo
        (mega.advanceControls prefixState (env 0))
    } = _
  rw [show env 0 = round by rfl]
  rw [hcontrols]
  exact hstep

/-- Guarded-left mirror of the rerooted first-letter checker-refresh packet. -/
theorem
    profiledRawJointHybridMegaGuardedLinked_leftPrefix_firstBoth_word_step_eq_refreshedBoth
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
    (tail : EnvironmentSequence In₁ In₂)
    (oldRoot : ProfiledRawJointHybridMegaGuardedLeftTargetRoot A strategy hwin
      initialBank)
    (holdRoot :
      profiledRawJointHybridGuardedLeftReceiverTargetRoot? A strategy hwin
          initialBank
          (profiledRawJointHybridGuardedLeftPrefixReceiverAfter A strategy
            hwin installation past input) = some oldRoot)
    (refreshedRoot :
      ProfiledRawJointHybridMegaGuardedLeftTargetRoot A strategy hwin
        initialBank)
    (hrefreshedRoot :
      profiledRawJointHybridGuardedLeftReceiverTargetRoot? A strategy hwin
          initialBank
          (profiledRawJointHybridGuardedLeftPrefixReceiverAfter A strategy
            hwin installation (past ++ [input])
              (nextInputOne, nextInputTwo)) = some refreshedRoot) :
    let mega := MegaGuardedLinkedPhysicalController A strategy hwin
      controllers initialBank fallbackTag
    let prefixState :=
      profiledRawJointHybridMegaGuardedLinkedLeftPrefixControls A strategy
        hwin controllers initialBank fallbackTag installation past input
          oldOutputOne oldOutputTwo
    let env := OmegaWord.prependList
      [⟨nextInputOne, nextInputTwo, .both⟩] tail
    let word := (mega.globalMachine.reroot prefixState).globalMachineTraceWord
      mega.globalOutputOne mega.globalOutputTwo env
    A.step (pairedCodeStateForRow A .first oldRoot.2.slot.1.1) (word 0) =
      pairedCodeStateForRow A .both refreshedRoot.2.slot.1.1 := by
  dsimp only
  let mega := MegaGuardedLinkedPhysicalController A strategy hwin controllers
    initialBank fallbackTag
  let prefixState :=
    profiledRawJointHybridMegaGuardedLinkedLeftPrefixControls A strategy hwin
      controllers initialBank fallbackTag installation past input oldOutputOne
        oldOutputTwo
  let round : EnvironmentRound In₁ In₂ :=
    ⟨nextInputOne, nextInputTwo, .both⟩
  let env : EnvironmentSequence In₁ In₂ :=
    OmegaWord.prependList [round] tail
  have hcontrols :=
    profiledRawJointHybridMegaGuardedLinked_leftPrefix_firstBoth_mixed A
      strategy hwin controllers initialBank fallbackTag installation past
        input oldOutputOne oldOutputTwo nextInputOne nextInputTwo oldRoot
          holdRoot
  have hstep :=
    profiledRawJointHybridMegaGuarded_leftPrefix_firstBoth_step_eq_refreshedBoth
      A strategy hwin initialBank installation past input
        (nextInputOne, nextInputTwo) oldRoot holdRoot refreshedRoot
          hrefreshedRoot
  dsimp only at hcontrols hstep
  change A.step (pairedCodeStateForRow A .first oldRoot.2.slot.1.1)
      {
        inputOne := nextInputOne
        inputTwo := nextInputTwo
        graph := .both
        outputOne := mega.globalOutputOne
          ((mega.globalMachine.reroot prefixState).globalStateTrace env 1)
        outputTwo := mega.globalOutputTwo
          ((mega.globalMachine.reroot prefixState).globalStateTrace env 1)
      } = pairedCodeStateForRow A .both refreshedRoot.2.slot.1.1
  rw [show 1 = 0 + 1 by omega,
    FiniteGlobalRoundMachine.globalStateTrace_succ]
  change A.step _
    {
      inputOne := nextInputOne
      inputTwo := nextInputTwo
      graph := .both
      outputOne := mega.globalOutputOne
        (mega.advanceControls prefixState (env 0))
      outputTwo := mega.globalOutputTwo
        (mega.advanceControls prefixState (env 0))
    } = _
  rw [show env 0 = round by rfl]
  rw [hcontrols]
  exact hstep

/-! ## Actual-execution refresh packets -/

/-- At any reached coupled cut followed by a nonempty right prefix and one
simultaneous round, the actual global DPA run reaches the refreshed target's
`.both` coordinate.  Both the old and refreshed root lookups are retained in
the conclusion for the subsequent physical splice. -/
theorem
    exists_profiledRawJointHybridMegaGuarded_actualRightPrefix_firstBoth_run_eq_refreshedBoth
    (controllers :
      ProfiledRawJointRootCompatibleInitialControllers A strategy)
    (fallbackTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (env : EnvironmentSequence In₁ In₂) (start n : Nat)
    (hphysical :
      (MegaGuardedLinkedPhysicalController A strategy hwin controllers
        initialBank fallbackTag).globalMachine.globalStateTrace env start =
        profiledRawJointHybridMegaGuardedCoupledControls A strategy hwin
          controllers initialBank fallbackTag installation oldOutputOne
            oldOutputTwo)
    (hentry :
      let pair := profiledRawJointHybridGuardedCommonPairAt A strategy hwin
        installation
      let mega := MegaGuardedLinkedPhysicalController A strategy hwin
        controllers initialBank fallbackTag
      A.run
          (mega.globalMachine.globalMachineTraceWord mega.globalOutputOne
            mega.globalOutputTwo env) start =
        pairedCodeStateForRow A .both pair.1.1.1.base.source.1.1)
    (hright : ∀ k : Nat, k < n + 1 →
      (env (start + k)).graph = .right)
    (hboth : (env (start + (n + 1))).graph = .both) :
    let inputs : Nat → In₂ × In₁ := fun k ↦
      ((env (start + k)).inputTwo, (env (start + k)).inputOne)
    let past := omegaPrefix inputs n
    let input := inputs n
    let cut := start + (n + 1)
    let mega := MegaGuardedLinkedPhysicalController A strategy hwin
      controllers initialBank fallbackTag
    ∃ oldRoot :
        ProfiledRawJointHybridMegaGuardedRightTargetRoot A strategy hwin
          initialBank,
      ∃ refreshedRoot :
          ProfiledRawJointHybridMegaGuardedRightTargetRoot A strategy hwin
            initialBank,
        profiledRawJointHybridGuardedRightReceiverTargetRoot? A strategy hwin
            initialBank
            (profiledRawJointHybridGuardedRightPrefixReceiverAfter A strategy
              hwin installation past input) = some oldRoot ∧
        profiledRawJointHybridGuardedRightReceiverTargetRoot? A strategy hwin
            initialBank
            (profiledRawJointHybridGuardedRightPrefixReceiverAfter A strategy
              hwin installation (past ++ [input])
                ((env cut).inputTwo, (env cut).inputOne)) =
          some refreshedRoot ∧
        A.run
            (mega.globalMachine.globalMachineTraceWord mega.globalOutputOne
              mega.globalOutputTwo env) (cut + 1) =
          pairedCodeStateForRow A .both refreshedRoot.2.slot.1.1 := by
  classical
  dsimp only at hentry ⊢
  let mega := MegaGuardedLinkedPhysicalController A strategy hwin controllers
    initialBank fallbackTag
  let inputs : Nat → In₂ × In₁ := fun k ↦
    ((env (start + k)).inputTwo, (env (start + k)).inputOne)
  let past := omegaPrefix inputs n
  let input := inputs n
  let cut := start + (n + 1)
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
  change mega.globalMachine.globalStateTrace env cut =
      profiledRawJointHybridMegaGuardedLinkedRightPrefixControls A strategy
        hwin controllers initialBank fallbackTag installation past input
          outputOne outputTwo at hphysicalEnd
  obtain ⟨oldRoot, holdRoot⟩ :=
    exists_profiledRawJointHybridGuardedRightPrefixReceiverAfter_targetRoot A
      strategy hwin initialBank installation past input
  obtain ⟨refreshedRoot, hrefreshedRoot⟩ :=
    exists_profiledRawJointHybridGuardedRightPrefixReceiverAfter_targetRoot A
      strategy hwin initialBank installation (past ++ [input])
        ((env cut).inputTwo, (env cut).inputOne)
  refine ⟨oldRoot, refreshedRoot, holdRoot, hrefreshedRoot, ?_⟩
  have hcheckerEnd :=
    profiledRawJointHybridMegaGuarded_actualRightPrefix_run_eq_targetFirst A
      strategy hwin controllers initialBank fallbackTag installation
        oldOutputOne oldOutputTwo env start n hphysical hentry hright oldRoot
          holdRoot
  change A.run
      (mega.globalMachine.globalMachineTraceWord mega.globalOutputOne
        mega.globalOutputTwo env) cut =
    pairedCodeStateForRow A .first oldRoot.2.slot.1.1 at hcheckerEnd
  cases hround : env cut with
  | mk nextInputOne nextInputTwo graph =>
      rw [hround] at hboth
      change graph = .both at hboth
      subst graph
      let round : EnvironmentRound In₁ In₂ :=
        ⟨nextInputOne, nextInputTwo, .both⟩
      let tail : EnvironmentSequence In₁ In₂ :=
        OmegaWord.drop env (cut + 1)
      have henv : OmegaWord.drop env cut =
          OmegaWord.prependList [round] tail := by
        funext k
        cases k with
        | zero => simpa [OmegaWord.drop, round] using hround
        | succ k =>
            simp only [OmegaWord.prependList_cons_succ,
              OmegaWord.prependList_nil, OmegaWord.drop, tail]
            congr 1
            omega
      have hwordStep :=
        profiledRawJointHybridMegaGuardedLinked_rightPrefix_firstBoth_word_step_eq_refreshedBoth
          A strategy hwin initialBank controllers fallbackTag installation past
            input outputOne outputTwo nextInputOne nextInputTwo tail oldRoot
              holdRoot refreshedRoot (by simpa [hround] using hrefreshedRoot)
      dsimp only at hwordStep
      let prefixState :=
        profiledRawJointHybridMegaGuardedLinkedRightPrefixControls A strategy
          hwin controllers initialBank fallbackTag installation past input
            outputOne outputTwo
      have hreroot := mega.globalMachine.reroot_globalMachineTraceWord_drop
        mega.globalOutputOne mega.globalOutputTwo env cut
      rw [hphysicalEnd, henv] at hreroot
      have hletter := congrFun hreroot 0
      have hletter' :
          ((mega.globalMachine.reroot prefixState).globalMachineTraceWord
              mega.globalOutputOne mega.globalOutputTwo
              (OmegaWord.prependList [round] tail)) 0 =
            (mega.globalMachine.globalMachineTraceWord mega.globalOutputOne
              mega.globalOutputTwo env) cut := by
        simpa [OmegaWord.drop] using hletter
      rw [run_succ, hcheckerEnd, ← hletter']
      exact hwordStep

/-- Actual-execution guarded-left mirror of the first-simultaneous refresh
packet. -/
theorem
    exists_profiledRawJointHybridMegaGuarded_actualLeftPrefix_firstBoth_run_eq_refreshedBoth
    (controllers :
      ProfiledRawJointRootCompatibleInitialControllers A strategy)
    (fallbackTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (env : EnvironmentSequence In₁ In₂) (start n : Nat)
    (hphysical :
      (MegaGuardedLinkedPhysicalController A strategy hwin controllers
        initialBank fallbackTag).globalMachine.globalStateTrace env start =
        profiledRawJointHybridMegaGuardedCoupledControls A strategy hwin
          controllers initialBank fallbackTag installation oldOutputOne
            oldOutputTwo)
    (hentry :
      let pair := profiledRawJointHybridGuardedCommonPairAt A strategy hwin
        installation
      let mega := MegaGuardedLinkedPhysicalController A strategy hwin
        controllers initialBank fallbackTag
      A.run
          (mega.globalMachine.globalMachineTraceWord mega.globalOutputOne
            mega.globalOutputTwo env) start =
        pairedCodeStateForRow A .both pair.1.2.1.base.source.1.1)
    (hleft : ∀ k : Nat, k < n + 1 →
      (env (start + k)).graph = .left)
    (hboth : (env (start + (n + 1))).graph = .both) :
    let inputs : Nat → In₁ × In₂ := fun k ↦
      ((env (start + k)).inputOne, (env (start + k)).inputTwo)
    let past := omegaPrefix inputs n
    let input := inputs n
    let cut := start + (n + 1)
    let mega := MegaGuardedLinkedPhysicalController A strategy hwin
      controllers initialBank fallbackTag
    ∃ oldRoot :
        ProfiledRawJointHybridMegaGuardedLeftTargetRoot A strategy hwin
          initialBank,
      ∃ refreshedRoot :
          ProfiledRawJointHybridMegaGuardedLeftTargetRoot A strategy hwin
            initialBank,
        profiledRawJointHybridGuardedLeftReceiverTargetRoot? A strategy hwin
            initialBank
            (profiledRawJointHybridGuardedLeftPrefixReceiverAfter A strategy
              hwin installation past input) = some oldRoot ∧
        profiledRawJointHybridGuardedLeftReceiverTargetRoot? A strategy hwin
            initialBank
            (profiledRawJointHybridGuardedLeftPrefixReceiverAfter A strategy
              hwin installation (past ++ [input])
                ((env cut).inputOne, (env cut).inputTwo)) =
          some refreshedRoot ∧
        A.run
            (mega.globalMachine.globalMachineTraceWord mega.globalOutputOne
              mega.globalOutputTwo env) (cut + 1) =
          pairedCodeStateForRow A .both refreshedRoot.2.slot.1.1 := by
  classical
  dsimp only at hentry ⊢
  let mega := MegaGuardedLinkedPhysicalController A strategy hwin controllers
    initialBank fallbackTag
  let inputs : Nat → In₁ × In₂ := fun k ↦
    ((env (start + k)).inputOne, (env (start + k)).inputTwo)
  let past := omegaPrefix inputs n
  let input := inputs n
  let cut := start + (n + 1)
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
  change mega.globalMachine.globalStateTrace env cut =
      profiledRawJointHybridMegaGuardedLinkedLeftPrefixControls A strategy
        hwin controllers initialBank fallbackTag installation past input
          outputOne outputTwo at hphysicalEnd
  obtain ⟨oldRoot, holdRoot⟩ :=
    exists_profiledRawJointHybridGuardedLeftPrefixReceiverAfter_targetRoot A
      strategy hwin initialBank installation past input
  obtain ⟨refreshedRoot, hrefreshedRoot⟩ :=
    exists_profiledRawJointHybridGuardedLeftPrefixReceiverAfter_targetRoot A
      strategy hwin initialBank installation (past ++ [input])
        ((env cut).inputOne, (env cut).inputTwo)
  refine ⟨oldRoot, refreshedRoot, holdRoot, hrefreshedRoot, ?_⟩
  have hcheckerEnd :=
    profiledRawJointHybridMegaGuarded_actualLeftPrefix_run_eq_targetFirst A
      strategy hwin controllers initialBank fallbackTag installation
        oldOutputOne oldOutputTwo env start n hphysical hentry hleft oldRoot
          holdRoot
  change A.run
      (mega.globalMachine.globalMachineTraceWord mega.globalOutputOne
        mega.globalOutputTwo env) cut =
    pairedCodeStateForRow A .first oldRoot.2.slot.1.1 at hcheckerEnd
  cases hround : env cut with
  | mk nextInputOne nextInputTwo graph =>
      rw [hround] at hboth
      change graph = .both at hboth
      subst graph
      let round : EnvironmentRound In₁ In₂ :=
        ⟨nextInputOne, nextInputTwo, .both⟩
      let tail : EnvironmentSequence In₁ In₂ :=
        OmegaWord.drop env (cut + 1)
      have henv : OmegaWord.drop env cut =
          OmegaWord.prependList [round] tail := by
        funext k
        cases k with
        | zero => simpa [OmegaWord.drop, round] using hround
        | succ k =>
            simp only [OmegaWord.prependList_cons_succ,
              OmegaWord.prependList_nil, OmegaWord.drop, tail]
            congr 1
            omega
      have hwordStep :=
        profiledRawJointHybridMegaGuardedLinked_leftPrefix_firstBoth_word_step_eq_refreshedBoth
          A strategy hwin initialBank controllers fallbackTag installation past
            input outputOne outputTwo nextInputOne nextInputTwo tail oldRoot
              holdRoot refreshedRoot (by simpa [hround] using hrefreshedRoot)
      dsimp only at hwordStep
      let prefixState :=
        profiledRawJointHybridMegaGuardedLinkedLeftPrefixControls A strategy
          hwin controllers initialBank fallbackTag installation past input
            outputOne outputTwo
      have hreroot := mega.globalMachine.reroot_globalMachineTraceWord_drop
        mega.globalOutputOne mega.globalOutputTwo env cut
      rw [hphysicalEnd, henv] at hreroot
      have hletter := congrFun hreroot 0
      have hletter' :
          ((mega.globalMachine.reroot prefixState).globalMachineTraceWord
              mega.globalOutputOne mega.globalOutputTwo
              (OmegaWord.prependList [round] tail)) 0 =
            (mega.globalMachine.globalMachineTraceWord mega.globalOutputOne
              mega.globalOutputTwo env) cut := by
        simpa [OmegaWord.drop] using hletter
      rw [run_succ, hcheckerEnd, ← hletter']
      exact hwordStep

end

end DetParityAutomaton

end DistributedSynthesis
