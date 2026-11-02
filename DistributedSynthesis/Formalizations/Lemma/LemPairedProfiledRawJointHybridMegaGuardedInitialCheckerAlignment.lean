/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridMegaGuardedCoupledStrictAcceptance
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCombinedFreshPhaseActivatedTwoRoundFront

/-!
# Honest checker alignment at the guarded mega entry

The first two simultaneous rounds of the guarded mega controller retain the
actual two input pairs, install the corresponding guarded sibling pair, and
emit the literal strategy outputs.  Consequently the physical coupled cut
and the DPA checker at that cut refer to one and the same root-pinned world.
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

/-! ## The semantic source selected by the physical seed -/

/-- The initial guarded installation and the phase-activated seed identify
the same literal source state. -/
theorem profiledRawJointHybridMegaGuarded_initialPair_source_eq_twoRound
    (first current : In₁ × In₂) :
    let installation :
        ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin :=
      .inl ⟨first, current⟩
    let pair := profiledRawJointHybridGuardedCommonPairAt A strategy hwin
      installation
    pairedCodeStateForRow A .both pair.1.1.1.base.source.1.1 =
      pairedCodeStateForRow A .both
        (((ProfiledRawJointGuardedCommonDecoratedPolicyPackage.literalCombinedFreshPhaseActivatedPointOfSeed
          A strategy
            (first, current)).world A strategy).procOneSlot A).1.1 :=
  rfl

set_option maxHeartbeats 1000000 in
/-- Two actual simultaneous rounds put the guarded mega controller in the
coupled state indexed by exactly those two input pairs. -/
theorem profiledRawJointHybridMegaGuarded_globalStateTrace_two
    (fallbackTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (first current : In₁ × In₂)
    (hfirst : env 0 = ⟨first.1, first.2, Graph.both⟩)
    (hcurrent : env 1 = ⟨current.1, current.2, Graph.both⟩) :
    let mega := Mega A strategy hwin controllers initialBank fallbackTag
    mega.globalMachine.globalStateTrace env 2 =
      profiledRawJointHybridMegaGuardedCoupledControls A strategy hwin
        controllers initialBank fallbackTag (.inl ⟨first, current⟩)
          (profiledRawJointInitialCommonBothOutput A strategy
            (first, current)).1
          (profiledRawJointInitialCommonBothOutput A strategy
            (first, current)).2 := by
  dsimp only
  rw [show 2 = 1 + 1 by omega,
    FiniteGlobalRoundMachine.globalStateTrace_succ,
    FiniteGlobalRoundMachine.globalStateTrace_succ, hfirst, hcurrent]
  rw [FiniteGlobalRoundMachine.globalStateTrace_zero]
  simp only [FinitePairedPhysicalController.globalMachine_initial,
    FinitePairedPhysicalController.globalMachine_step]
  rw [profiledRawJointHybridMegaGuardedLinked_root_both A strategy hwin
    controllers initialBank fallbackTag first.1 first.2]
  simp only [Prod.eta]
  refine (profiledRawJointHybridMegaGuardedLinked_initialShadows_both A
    strategy hwin controllers initialBank fallbackTag
      (profiledRawJointHybridInitialRootRecvOne A strategy hwin controllers
        first).2
      (profiledRawJointHybridInitialRootRecvTwo A strategy hwin controllers
        first).2
      (profiledRawJointHybridInitialRootRecvOne A strategy hwin controllers
        first).1
      (profiledRawJointHybridInitialRootRecvTwo A strategy hwin controllers
        first).1 current.1 current.2).trans ?_
  have houtputs :=
    profiledRawJointHybridInitialToSecondShadows_outputs A strategy hwin
      controllers first current
  have hone :
      (profiledRawJointHybridInitialToSecondOneShadow A strategy hwin
        controllers
        (profiledRawJointHybridInitialRootRecvTwo A strategy hwin controllers
          first).2 current.1 current.2).1 =
        (profiledRawJointInitialCommonBothOutput A strategy
          (first, current)).1 := by
    simpa only [Prod.fst] using congrArg Prod.fst houtputs
  have htwo :
      (profiledRawJointHybridInitialToSecondTwoShadow A strategy hwin
        controllers
        (profiledRawJointHybridInitialRootRecvOne A strategy hwin controllers
          first).2 current.2 current.1).1 =
        (profiledRawJointInitialCommonBothOutput A strategy
          (first, current)).2 := by
    simpa only [Prod.snd] using congrArg Prod.snd houtputs
  simp only [profiledRawJointHybridMegaInitialToCoupledOne,
    profiledRawJointHybridMegaInitialToCoupledTwo]
  rw [hone, htwo]
  rfl

/-! ## The two emitted letters are the literal strategy prefix -/

/-- The post-transition Moore outputs of the first mega round are the literal
first simultaneous outputs. -/
theorem profiledRawJointHybridMegaGuarded_outputs_after_one
    (fallbackTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (first : In₁ × In₂)
    (hfirst : env 0 = ⟨first.1, first.2, Graph.both⟩) :
    let mega := Mega A strategy hwin controllers initialBank fallbackTag
    (mega.globalOutputOne (mega.globalMachine.globalStateTrace env 1),
      mega.globalOutputTwo (mega.globalMachine.globalStateTrace env 1)) =
      let round := nextRound strategy []
        ⟨first.1, first.2, Graph.both⟩
      (round.outputOne, round.outputTwo) := by
  dsimp only
  rw [FiniteGlobalRoundMachine.globalStateTrace_succ,
    FiniteGlobalRoundMachine.globalStateTrace_zero, hfirst]
  simp only [FinitePairedPhysicalController.globalMachine_initial,
    FinitePairedPhysicalController.globalMachine_step]
  rw [profiledRawJointHybridMegaGuardedLinked_root_both A strategy hwin
    controllers initialBank fallbackTag first.1 first.2]
  change
    ((profiledRawJointHybridInitialRootRecvOne A strategy hwin controllers
      (first.1, first.2)).1,
      (profiledRawJointHybridInitialRootRecvTwo A strategy hwin controllers
        (first.1, first.2)).1) = _
  simpa only [Prod.eta] using
    profiledRawJointHybridInitialRootRecv_outputs_eq_literalBoth A strategy
      hwin controllers first

/-- The post-transition Moore outputs of the second mega round are the exact
literal common one-shot outputs selected by the two received input pairs. -/
theorem profiledRawJointHybridMegaGuarded_outputs_after_two
    (fallbackTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (first current : In₁ × In₂)
    (hfirst : env 0 = ⟨first.1, first.2, Graph.both⟩)
    (hcurrent : env 1 = ⟨current.1, current.2, Graph.both⟩) :
    let mega := Mega A strategy hwin controllers initialBank fallbackTag
    (mega.globalOutputOne (mega.globalMachine.globalStateTrace env 2),
      mega.globalOutputTwo (mega.globalMachine.globalStateTrace env 2)) =
      profiledRawJointInitialCommonBothOutput A strategy
        (first, current) := by
  dsimp only
  rw [profiledRawJointHybridMegaGuarded_globalStateTrace_two A strategy hwin
    controllers initialBank fallbackTag env first current hfirst hcurrent]
  rfl

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- The one-shot output stored at the coupled cut is definitionally the
second letter of the literal two-round strategy execution. -/
theorem profiledRawJointHybridMegaGuarded_initialCommonOutput_eq_secondRound
    (first current : In₁ × In₂) :
    profiledRawJointInitialCommonBothOutput A strategy (first, current) =
      let firstRound := nextRound strategy []
        ⟨first.1, first.2, Graph.both⟩
      let secondRound := nextRound strategy [firstRound]
        ⟨current.1, current.2, Graph.both⟩
      (secondRound.outputOne, secondRound.outputTwo) :=
  rfl

/-- The first letter of the actual mega trace word is the first literal
strategy round. -/
theorem profiledRawJointHybridMegaGuarded_traceWord_zero
    (fallbackTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (first : In₁ × In₂)
    (hfirst : env 0 = ⟨first.1, first.2, Graph.both⟩) :
    let mega := Mega A strategy hwin controllers initialBank fallbackTag
    mega.globalMachine.globalMachineTraceWord mega.globalOutputOne
        mega.globalOutputTwo env 0 =
      nextRound strategy [] ⟨first.1, first.2, Graph.both⟩ := by
  dsimp only
  have houtputs :=
    profiledRawJointHybridMegaGuarded_outputs_after_one A strategy hwin
      controllers initialBank fallbackTag env first hfirst
  have hone :
      (Mega A strategy hwin controllers initialBank fallbackTag).globalOutputOne
          ((Mega A strategy hwin controllers initialBank fallbackTag
            ).globalMachine.globalStateTrace env 1) =
        (nextRound strategy []
          ⟨first.1, first.2, Graph.both⟩).outputOne := by
    simpa only [Prod.fst] using congrArg Prod.fst houtputs
  have htwo :
      (Mega A strategy hwin controllers initialBank fallbackTag).globalOutputTwo
          ((Mega A strategy hwin controllers initialBank fallbackTag
            ).globalMachine.globalStateTrace env 1) =
        (nextRound strategy []
          ⟨first.1, first.2, Graph.both⟩).outputTwo := by
    simpa only [Prod.snd] using congrArg Prod.snd houtputs
  simp only [FiniteGlobalRoundMachine.globalMachineTraceWord]
  rw [hfirst, hone, htwo]
  rfl

/-- The second letter of the actual mega trace word is the second literal
strategy round. -/
theorem profiledRawJointHybridMegaGuarded_traceWord_one
    (fallbackTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (first current : In₁ × In₂)
    (hfirst : env 0 = ⟨first.1, first.2, Graph.both⟩)
    (hcurrent : env 1 = ⟨current.1, current.2, Graph.both⟩) :
    let mega := Mega A strategy hwin controllers initialBank fallbackTag
    mega.globalMachine.globalMachineTraceWord mega.globalOutputOne
        mega.globalOutputTwo env 1 =
      let firstRound := nextRound strategy []
        ⟨first.1, first.2, Graph.both⟩
      nextRound strategy [firstRound]
        ⟨current.1, current.2, Graph.both⟩ := by
  dsimp only
  have houtputs :=
    profiledRawJointHybridMegaGuarded_outputs_after_two A strategy hwin
      controllers initialBank fallbackTag env first current hfirst hcurrent
  rw [profiledRawJointHybridMegaGuarded_initialCommonOutput_eq_secondRound A
    strategy first current] at houtputs
  have hone :
      (Mega A strategy hwin controllers initialBank fallbackTag).globalOutputOne
          ((Mega A strategy hwin controllers initialBank fallbackTag
            ).globalMachine.globalStateTrace env 2) =
        (nextRound strategy
          [nextRound strategy [] ⟨first.1, first.2, Graph.both⟩]
          ⟨current.1, current.2, Graph.both⟩).outputOne := by
    simpa only [Prod.fst] using congrArg Prod.fst houtputs
  have htwo :
      (Mega A strategy hwin controllers initialBank fallbackTag).globalOutputTwo
          ((Mega A strategy hwin controllers initialBank fallbackTag
            ).globalMachine.globalStateTrace env 2) =
        (nextRound strategy
          [nextRound strategy [] ⟨first.1, first.2, Graph.both⟩]
          ⟨current.1, current.2, Graph.both⟩).outputTwo := by
    simpa only [Prod.snd] using congrArg Prod.snd houtputs
  simp only [FiniteGlobalRoundMachine.globalMachineTraceWord]
  rw [hcurrent]
  change
    RoundRecord.mk current.1 current.2 Graph.both
        ((Mega A strategy hwin controllers initialBank fallbackTag
          ).globalOutputOne
          ((Mega A strategy hwin controllers initialBank fallbackTag
            ).globalMachine.globalStateTrace env 2))
        ((Mega A strategy hwin controllers initialBank fallbackTag
          ).globalOutputTwo
          ((Mega A strategy hwin controllers initialBank fallbackTag
            ).globalMachine.globalStateTrace env 2)) = _
  rw [hone, htwo]
  rfl

/-! ## Honest DPA alignment at the coupled cut -/

/-- After the same two physical rounds, the actual DPA run is the checker
source stored by the guarded installation reached by the controller. -/
theorem profiledRawJointHybridMegaGuarded_run_two_eq_coupledSource
    (fallbackTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (first current : In₁ × In₂)
    (hfirst : env 0 = ⟨first.1, first.2, Graph.both⟩)
    (hcurrent : env 1 = ⟨current.1, current.2, Graph.both⟩) :
    let mega := Mega A strategy hwin controllers initialBank fallbackTag
    let installation :
        ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin :=
      .inl ⟨first, current⟩
    let pair := profiledRawJointHybridGuardedCommonPairAt A strategy hwin
      installation
    A.run
        (mega.globalMachine.globalMachineTraceWord mega.globalOutputOne
          mega.globalOutputTwo env) 2 =
      pairedCodeStateForRow A .both pair.1.1.1.base.source.1.1 := by
  dsimp only
  let mega := Mega A strategy hwin controllers initialBank fallbackTag
  let word := mega.globalMachine.globalMachineTraceWord mega.globalOutputOne
    mega.globalOutputTwo env
  have hrun :=
    ProfiledRawJointGuardedCommonDecoratedPolicyPackage.literalCombinedFreshPhaseActivatedTwoRound_run_two_eq_installedState
      A strategy first current word
        (profiledRawJointHybridMegaGuarded_traceWord_zero A strategy hwin
          controllers initialBank fallbackTag env first hfirst)
        (profiledRawJointHybridMegaGuarded_traceWord_one A strategy hwin
          controllers initialBank fallbackTag env first current hfirst hcurrent)
  change A.run word 2 = _
  calc
    A.run word 2 =
        pairedCodeStateForRow A .both
          (((ProfiledRawJointGuardedCommonDecoratedPolicyPackage.literalCombinedFreshPhaseActivatedPointOfSeed
            A strategy (first, current)).world A strategy).procOneSlot A).1.1 :=
      hrun
    _ = pairedCodeStateForRow A .both
        (profiledRawJointHybridGuardedCommonPairAt A strategy hwin
          (.inl ⟨first, current⟩)).1.1.1.base.source.1.1 :=
      (profiledRawJointHybridMegaGuarded_initialPair_source_eq_twoRound A
        strategy hwin first current).symm

/-! ## Acceptance of the immediate all-strict suffix -/

/-- If no further simultaneous graph occurs after the honest two-round seed,
the already established guarded strict-suffix theorem applies directly to
the actual mega execution. -/
theorem profiledRawJointHybridMegaGuarded_accepts_of_noBoth_after_two
    (fallbackTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (first current : In₁ × In₂)
    (hfirst : env 0 = ⟨first.1, first.2, Graph.both⟩)
    (hcurrent : env 1 = ⟨current.1, current.2, Graph.both⟩)
    (hnoboth : ∀ k : Nat, (env (2 + k)).graph ≠ .both) :
    let mega := Mega A strategy hwin controllers initialBank fallbackTag
    A.Accepts
      (mega.globalMachine.globalMachineTraceWord mega.globalOutputOne
        mega.globalOutputTwo env) := by
  dsimp only
  apply profiledRawJointHybridMegaGuarded_accepts_of_coupled_noBoth A
    strategy hwin controllers initialBank fallbackTag (.inl ⟨first, current⟩)
      (profiledRawJointInitialCommonBothOutput A strategy
        (first, current)).1
      (profiledRawJointInitialCommonBothOutput A strategy
        (first, current)).2 env 2
  · exact profiledRawJointHybridMegaGuarded_globalStateTrace_two A strategy
      hwin controllers initialBank fallbackTag env first current hfirst
        hcurrent
  · exact profiledRawJointHybridMegaGuarded_run_two_eq_coupledSource A
      strategy hwin controllers initialBank fallbackTag env first current
        hfirst hcurrent
  · exact hnoboth

/-! ## Checker preservation at every guarded child handoff -/

/-- At the end of any actual nonempty guarded-right prefix, the current DPA
state is exactly the `.first` coordinate of the child root selected by the
receiver.  This is the honest pre-close handoff invariant, stated on the
whole mega execution rather than on the isolated finite monitor. -/
theorem profiledRawJointHybridMegaGuarded_actualRightPrefix_run_eq_targetFirst
    (fallbackTag : RetainedTag A strategy hwin)
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (env : EnvironmentSequence In₁ In₂) (start n : Nat)
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
    (hright : ∀ k : Nat, k < n + 1 →
      (env (start + k)).graph = .right)
    (root : ProfiledRawJointHybridMegaGuardedRightTargetRoot A strategy hwin
      initialBank)
    (hroot :
      let inputs : Nat → In₂ × In₁ := fun k ↦
        ((env (start + k)).inputTwo, (env (start + k)).inputOne)
      profiledRawJointHybridGuardedRightReceiverTargetRoot? A strategy hwin
          initialBank
          (profiledRawJointHybridGuardedRightPrefixReceiverAfter A strategy
            hwin installation (omegaPrefix inputs n) (inputs n)) =
        some root) :
    let mega := Mega A strategy hwin controllers initialBank fallbackTag
    A.run
        (mega.globalMachine.globalMachineTraceWord mega.globalOutputOne
          mega.globalOutputTwo env) (start + (n + 1)) =
      pairedCodeStateForRow A .first root.2.slot.1.1 := by
  dsimp only at hentry hroot ⊢
  let inputs : Nat → In₂ × In₁ := fun k ↦
    ((env (start + k)).inputTwo, (env (start + k)).inputOne)
  have hscan :=
    profiledRawJointHybridMegaGuarded_actualRightPrefix_run_eq_scanCurrent A
      strategy hwin controllers initialBank fallbackTag installation
        oldOutputOne oldOutputTwo env start n hphysical hentry hright
  have htarget :=
    profiledRawJointHybridMegaGuardedRightPrefixTargetRoot_first_eq_scanCurrent
      A strategy hwin initialBank installation (omegaPrefix inputs n)
        (inputs n) root hroot
  exact hscan.trans htarget.symm

/-- Guarded-left mirror of the exact pre-close checker alignment. -/
theorem profiledRawJointHybridMegaGuarded_actualLeftPrefix_run_eq_targetFirst
    (fallbackTag : RetainedTag A strategy hwin)
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (env : EnvironmentSequence In₁ In₂) (start n : Nat)
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
    (hleft : ∀ k : Nat, k < n + 1 →
      (env (start + k)).graph = .left)
    (root : ProfiledRawJointHybridMegaGuardedLeftTargetRoot A strategy hwin
      initialBank)
    (hroot :
      let inputs : Nat → In₁ × In₂ := fun k ↦
        ((env (start + k)).inputOne, (env (start + k)).inputTwo)
      profiledRawJointHybridGuardedLeftReceiverTargetRoot? A strategy hwin
          initialBank
          (profiledRawJointHybridGuardedLeftPrefixReceiverAfter A strategy
            hwin installation (omegaPrefix inputs n) (inputs n)) =
        some root) :
    let mega := Mega A strategy hwin controllers initialBank fallbackTag
    A.run
        (mega.globalMachine.globalMachineTraceWord mega.globalOutputOne
          mega.globalOutputTwo env) (start + (n + 1)) =
      pairedCodeStateForRow A .first root.2.slot.1.1 := by
  dsimp only at hentry hroot ⊢
  let inputs : Nat → In₁ × In₂ := fun k ↦
    ((env (start + k)).inputOne, (env (start + k)).inputTwo)
  have hscan :=
    profiledRawJointHybridMegaGuarded_actualLeftPrefix_run_eq_scanCurrent A
      strategy hwin controllers initialBank fallbackTag installation
        oldOutputOne oldOutputTwo env start n hphysical hentry hleft
  have htarget :=
    profiledRawJointHybridMegaGuardedLeftPrefixTargetRoot_first_eq_scanCurrent
      A strategy hwin initialBank installation (omegaPrefix inputs n)
        (inputs n) root hroot
  exact hscan.trans htarget.symm

/-! ## First-simultaneous checker refresh -/

/-- Once the closing endpoint is identified with the delayed-overlap output,
the first simultaneous round advances the old strict-prefix `.first` checker
to the refreshed target's `.both` coordinate.  The other output equation is
already supplied by the guarded receiver trajectory. -/
theorem
    profiledRawJointHybridMegaGuarded_rightPrefix_firstBoth_step_eq_refreshedBoth_of_closingOutput
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
        some refreshedRoot)
    (hclosing :
      let source := profiledRawJointHybridMegaChildSource A strategy hwin
        initialBank oldRoot.1
      let policy := profiledRawJointHybridMegaChildPolicy A strategy hwin
        initialBank oldRoot.1
      let bank := profiledRawJointHybridMegaChildControllerBank A strategy hwin
        initialBank oldRoot.1
      let restart := profiledRawJointUnitRestartLeft A strategy source policy
        bank oldRoot.2 .first
      let nextLeft := continueProfiledRawJointUnitLeftPolicyReceiver A strategy
        source policy bank restart.2 restart.1 (nextInput.2, nextInput.1)
      let pair := profiledRawJointHybridGuardedCommonPairAt A strategy hwin
        installation
      let state := profiledRawJointGuardedCommonRightFiniteStateAfter A strategy
        hwin pair (past ++ [input])
      let monitor := profiledRawJointGuardedRightPhysicalSiblingMonitor A
        pair.1.1.1 false
      let controller := (pair.1.1).memberController A false
      let record := narrowedRecord monitor (controller.labelOf state.1) state.2
        nextInput
      nextLeft.1 = pairedRightClosingForRow .both
        (profiledRawJointTargetRightPhysicalLetter A record).2.1) :
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
  dsimp only at hclosing ⊢
  have hold :=
    profiledRawJointHybridMegaGuardedRightPrefixTargetRoot_first_eq_scanCurrent
      A strategy hwin initialBank installation past input oldRoot holdRoot
  have hrefreshed :=
    profiledRawJointHybridMegaGuardedRightPrefixTargetRoot_both_eq_scanCurrent
      A strategy hwin initialBank installation (past ++ [input]) nextInput
        refreshedRoot hrefreshedRoot
  have hinformed :=
    profiledRawJointHybridGuardedRightPrefixReceiverAfter_step_output A
      strategy hwin installation past input nextInput
  dsimp only at hold hrefreshed hinformed
  rw [profiledRawJointGuardedCommonRightFiniteStateAfter_append_one A strategy
    hwin (profiledRawJointHybridGuardedCommonPairAt A strategy hwin
      installation) past input] at hrefreshed
  rw [hold, hclosing, hinformed]
  rw [profiledRawJointGuardedCommonRightFiniteStateAfter_append_one A strategy
    hwin (profiledRawJointHybridGuardedCommonPairAt A strategy hwin
      installation) past input]
  exact hrefreshed.symm

/-- Guarded-left mirror: the closing process-two output is the only remaining
local equation needed to identify the first simultaneous checker refresh. -/
theorem
    profiledRawJointHybridMegaGuarded_leftPrefix_firstBoth_step_eq_refreshedBoth_of_closingOutput
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
        some refreshedRoot)
    (hclosing :
      let source := profiledRawJointHybridMegaChildSource A strategy hwin
        initialBank oldRoot.1
      let policy := profiledRawJointHybridMegaChildPolicy A strategy hwin
        initialBank oldRoot.1
      let bank := profiledRawJointHybridMegaChildControllerBank A strategy hwin
        initialBank oldRoot.1
      let restart := profiledRawJointUnitRestartRight A strategy source policy
        bank oldRoot.2 .first
      let nextRight := continueProfiledRawJointUnitRightPolicyReceiver A
        strategy source policy bank restart.2 restart.1
          (nextInput.2, nextInput.1)
      let pair := profiledRawJointHybridGuardedCommonPairAt A strategy hwin
        installation
      let state := profiledRawJointGuardedCommonLeftFiniteStateAfter A strategy
        hwin pair (past ++ [input])
      let monitor := profiledRawJointGuardedLeftPhysicalSiblingMonitor A
        pair.1.2.1 false
      let controller := (pair.1.2).memberController A false
      let record := narrowedRecord monitor (controller.labelOf state.1) state.2
        nextInput
      nextRight.1 = pairedLeftClosingForRow .both
        (profiledRawJointTargetLeftPhysicalLetter A record).2.1) :
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
  dsimp only at hclosing ⊢
  have hold :=
    profiledRawJointHybridMegaGuardedLeftPrefixTargetRoot_first_eq_scanCurrent
      A strategy hwin initialBank installation past input oldRoot holdRoot
  have hrefreshed :=
    profiledRawJointHybridMegaGuardedLeftPrefixTargetRoot_both_eq_scanCurrent
      A strategy hwin initialBank installation (past ++ [input]) nextInput
        refreshedRoot hrefreshedRoot
  have hinformed :=
    profiledRawJointHybridGuardedLeftPrefixReceiverAfter_step_output A strategy
      hwin installation past input nextInput
  dsimp only at hold hrefreshed hinformed
  rw [profiledRawJointGuardedCommonLeftFiniteStateAfter_append_one A strategy
    hwin (profiledRawJointHybridGuardedCommonPairAt A strategy hwin
      installation) past input] at hrefreshed
  rw [hold, hinformed, hclosing]
  rw [profiledRawJointGuardedCommonLeftFiniteStateAfter_append_one A strategy
    hwin (profiledRawJointHybridGuardedCommonPairAt A strategy hwin
      installation) past input]
  exact hrefreshed.symm

end

end DetParityAutomaton

end DistributedSynthesis
