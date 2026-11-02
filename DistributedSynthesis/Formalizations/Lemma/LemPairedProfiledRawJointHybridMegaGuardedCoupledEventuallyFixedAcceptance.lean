/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridMegaGuardedStrictEntryAlignment
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointUnitEventuallyFixedAcceptance

/-!
# Eventually fixed acceptance from an aligned guarded coupled cut

The first guarded strict reversal installs a fresh Unit child.  The Unit
eventual-fixed theorem then carries any finite number of further strict
reversals to the first permanently fixed block and closes the one-sided tail.
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

/-- A guarded-right close installs a fresh matched-left Unit state; every
eventually fixed all-strict continuation is accepted from its exact target
coordinate. -/
theorem
    profiledRawJointHybridMegaGuardedLinked_rightPrefix_leftClose_eventuallyFixed_acceptsFrom_first
    (fallbackTag : RetainedTag A strategy hwin)
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (nextInputOne : In₁) (nextInputTwo : In₂)
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (hhead : physicalEnv 0 = ⟨nextInputOne, nextInputTwo, .left⟩)
    (hnoboth : ∀ n : Nat, (physicalEnv n).graph ≠ .both)
    (heventual :
      EventuallyStrictRight (fun n ↦ (physicalEnv n).graph) ∨
        EventuallyStrictLeft (fun n ↦ (physicalEnv n).graph))
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
  let source := profiledRawJointHybridMegaChildSource A strategy hwin
    initialBank root.1
  let policy := profiledRawJointHybridMegaChildPolicy A strategy hwin
    initialBank root.1
  let bank := profiledRawJointHybridMegaChildControllerBank A strategy hwin
    initialBank root.1
  let adapter := UnitAdapter A strategy hwin controllers initialBank root.1
  let fresh := profiledRawJointUnitFreshMatchedLeftState A strategy source
    policy bank adapter root.2 .first oldOutputOne oldOutputTwo
  have hgraph : (physicalEnv 0).graph = .left := by
    simpa using congrArg EnvironmentRound.graph hhead
  have zero : ProfiledRawJointUnitStrictControlAtZero A strategy source policy
      bank adapter fresh physicalEnv .first (.inr root.2) := by
    change (physicalEnv 0).graph = .left ∧ _
    exact ⟨hgraph, Or.inl ⟨oldOutputOne, oldOutputTwo, rfl⟩⟩
  rcases heventual with hright | hleft
  · exact profiledRawJointUnit_eventuallyStrictRight_acceptsFrom A strategy
      source policy bank adapter fresh physicalEnv (.inr root.2) zero
        (pairedCodeStateForRow A .first root.2.slot.1.1) rfl hnoboth hright
  · exact profiledRawJointUnit_eventuallyStrictLeft_acceptsFrom A strategy
      source policy bank adapter fresh physicalEnv (.inr root.2) zero
        (pairedCodeStateForRow A .first root.2.slot.1.1) rfl hnoboth hleft

/-- Guarded-left / fresh matched-right mirror. -/
theorem
    profiledRawJointHybridMegaGuardedLinked_leftPrefix_rightClose_eventuallyFixed_acceptsFrom_first
    (fallbackTag : RetainedTag A strategy hwin)
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (past : List (In₁ × In₂)) (input : In₁ × In₂)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (nextInputOne : In₁) (nextInputTwo : In₂)
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (hhead : physicalEnv 0 = ⟨nextInputOne, nextInputTwo, .right⟩)
    (hnoboth : ∀ n : Nat, (physicalEnv n).graph ≠ .both)
    (heventual :
      EventuallyStrictRight (fun n ↦ (physicalEnv n).graph) ∨
        EventuallyStrictLeft (fun n ↦ (physicalEnv n).graph))
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
  let source := profiledRawJointHybridMegaChildSource A strategy hwin
    initialBank root.1
  let policy := profiledRawJointHybridMegaChildPolicy A strategy hwin
    initialBank root.1
  let bank := profiledRawJointHybridMegaChildControllerBank A strategy hwin
    initialBank root.1
  let adapter := UnitAdapter A strategy hwin controllers initialBank root.1
  let fresh := profiledRawJointUnitFreshMatchedRightState A strategy source
    policy bank adapter root.2 .first oldOutputOne oldOutputTwo
  have hgraph : (physicalEnv 0).graph = .right := by
    simpa using congrArg EnvironmentRound.graph hhead
  have zero : ProfiledRawJointUnitStrictControlAtZero A strategy source policy
      bank adapter fresh physicalEnv .first (.inl root.2) := by
    change (physicalEnv 0).graph = .right ∧ _
    exact ⟨hgraph, Or.inl ⟨oldOutputOne, oldOutputTwo, rfl⟩⟩
  rcases heventual with hright | hleft
  · exact profiledRawJointUnit_eventuallyStrictRight_acceptsFrom A strategy
      source policy bank adapter fresh physicalEnv (.inl root.2) zero
        (pairedCodeStateForRow A .first root.2.slot.1.1) rfl hnoboth hright
  · exact profiledRawJointUnit_eventuallyStrictLeft_acceptsFrom A strategy
      source policy bank adapter fresh physicalEnv (.inl root.2) zero
        (pairedCodeStateForRow A .first root.2.slot.1.1) rfl hnoboth hleft

/-! ## Actual-prefix splices -/

/-- Splice the right-prefix/left-close eventual-fixed child acceptance into
the complete Mega word at an actual physical cut. -/
theorem
    profiledRawJointHybridMegaGuardedLinked_accepts_of_rightPrefix_leftClose_eventuallyFixed
    (fallbackTag : RetainedTag A strategy hwin)
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (env : EnvironmentSequence In₁ In₂) (start : Nat)
    (nextInputOne : In₁) (nextInputTwo : In₂)
    (hhead : env start = ⟨nextInputOne, nextInputTwo, .left⟩)
    (hnoboth : ∀ n : Nat, (env (start + n)).graph ≠ .both)
    (heventual :
      EventuallyStrictRight (fun n ↦ (env (start + n)).graph) ∨
        EventuallyStrictLeft (fun n ↦ (env (start + n)).graph))
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
  rw [←
    profiledRawJointHybridMegaGuardedRightPrefixTargetRoot_first_eq_scanCurrent
      A strategy hwin initialBank installation past input root hroot]
  apply
    profiledRawJointHybridMegaGuardedLinked_rightPrefix_leftClose_eventuallyFixed_acceptsFrom_first
      A strategy hwin controllers initialBank fallbackTag installation past
        input oldOutputOne oldOutputTwo nextInputOne nextInputTwo
          (OmegaWord.drop env start) (root := root)
  · simpa [OmegaWord.drop] using hhead
  · intro n
    simpa [OmegaWord.drop, Nat.add_assoc] using hnoboth n
  · simpa [OmegaWord.drop, Nat.add_assoc] using heventual
  · exact hroot

/-- Actual guarded-left mirror. -/
theorem
    profiledRawJointHybridMegaGuardedLinked_accepts_of_leftPrefix_rightClose_eventuallyFixed
    (fallbackTag : RetainedTag A strategy hwin)
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (past : List (In₁ × In₂)) (input : In₁ × In₂)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (env : EnvironmentSequence In₁ In₂) (start : Nat)
    (nextInputOne : In₁) (nextInputTwo : In₂)
    (hhead : env start = ⟨nextInputOne, nextInputTwo, .right⟩)
    (hnoboth : ∀ n : Nat, (env (start + n)).graph ≠ .both)
    (heventual :
      EventuallyStrictRight (fun n ↦ (env (start + n)).graph) ∨
        EventuallyStrictLeft (fun n ↦ (env (start + n)).graph))
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
  rw [←
    profiledRawJointHybridMegaGuardedLeftPrefixTargetRoot_first_eq_scanCurrent
      A strategy hwin initialBank installation past input root hroot]
  apply
    profiledRawJointHybridMegaGuardedLinked_leftPrefix_rightClose_eventuallyFixed_acceptsFrom_first
      A strategy hwin controllers initialBank fallbackTag installation past
        input oldOutputOne oldOutputTwo nextInputOne nextInputTwo
          (OmegaWord.drop env start) (root := root)
  · simpa [OmegaWord.drop] using hhead
  · intro n
    simpa [OmegaWord.drop, Nat.add_assoc] using hnoboth n
  · simpa [OmegaWord.drop, Nat.add_assoc] using heventual
  · exact hroot

/-! ## Closing the first guarded reversal -/

/-- A finite guarded-right block followed by its first left reversal and an
eventually fixed strict Unit continuation accepts the complete Mega word. -/
theorem
    profiledRawJointHybridMegaGuarded_accepts_of_coupled_rightPrefix_leftClose_eventuallyFixed
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
    (hclose : (env (start + (n + 1))).graph = .left)
    (hnoboth : ∀ k : Nat,
      (env (start + (n + 1) + k)).graph ≠ .both)
    (heventual :
      EventuallyStrictRight
          (fun k ↦ (env (start + (n + 1) + k)).graph) ∨
        EventuallyStrictLeft
          (fun k ↦ (env (start + (n + 1) + k)).graph)) :
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
        profiledRawJointHybridMegaGuardedLinked_accepts_of_rightPrefix_leftClose_eventuallyFixed
          A strategy hwin controllers initialBank fallbackTag installation
            past input outputOne outputTwo env (start + (n + 1)) nextInputOne
              nextInputTwo hround (root := root)
      · simpa only [Nat.add_assoc] using hnoboth
      · simpa only [Nat.add_assoc] using heventual
      · exact hroot
      · exact hphysicalEnd
      · exact hcheckerEnd

/-- Guarded-left mirror. -/
theorem
    profiledRawJointHybridMegaGuarded_accepts_of_coupled_leftPrefix_rightClose_eventuallyFixed
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
    (hclose : (env (start + (n + 1))).graph = .right)
    (hnoboth : ∀ k : Nat,
      (env (start + (n + 1) + k)).graph ≠ .both)
    (heventual :
      EventuallyStrictRight
          (fun k ↦ (env (start + (n + 1) + k)).graph) ∨
        EventuallyStrictLeft
          (fun k ↦ (env (start + (n + 1) + k)).graph)) :
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
        profiledRawJointHybridMegaGuardedLinked_accepts_of_leftPrefix_rightClose_eventuallyFixed
          A strategy hwin controllers initialBank fallbackTag installation
            past input outputOne outputTwo env (start + (n + 1)) nextInputOne
              nextInputTwo hround (root := root)
      · simpa only [Nat.add_assoc] using hnoboth
      · simpa only [Nat.add_assoc] using heventual
      · exact hroot
      · exact hphysicalEnd
      · exact hcheckerEnd

/-! ## Complete eventually-fixed branch from the coupled cut -/

/-- From an aligned guarded coupled cut, every no-`.both` eventually fixed
strict tail is accepted.  If no first reversal exists, the original guarded
one-sided controller accepts directly; otherwise the reversal installs the
Unit carrier handled above. -/
theorem profiledRawJointHybridMegaGuarded_accepts_of_coupled_eventuallyFixed
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
    (hentryRight :
      let pair := profiledRawJointHybridGuardedCommonPairAt A strategy hwin
        installation
      let mega := Mega A strategy hwin controllers initialBank fallbackTag
      A.run
          (mega.globalMachine.globalMachineTraceWord mega.globalOutputOne
            mega.globalOutputTwo env) start =
        pairedCodeStateForRow A .both pair.1.1.1.base.source.1.1)
    (hnoboth : ∀ k : Nat, (env (start + k)).graph ≠ .both)
    (heventual :
      EventuallyStrictRight (fun k ↦ (env (start + k)).graph) ∨
        EventuallyStrictLeft (fun k ↦ (env (start + k)).graph)) :
    let mega := Mega A strategy hwin controllers initialBank fallbackTag
    A.Accepts
      (mega.globalMachine.globalMachineTraceWord mega.globalOutputOne
        mega.globalOutputTwo env) := by
  classical
  dsimp only at hentryRight ⊢
  let mega := Mega A strategy hwin controllers initialBank fallbackTag
  let graphs : Nat → Graph := fun k ↦ (env (start + k)).graph
  have hentryLeft :
      A.run
          (mega.globalMachine.globalMachineTraceWord mega.globalOutputOne
            mega.globalOutputTwo env) start =
        pairedCodeStateForRow A .both
          (profiledRawJointHybridGuardedCommonPairAt A strategy hwin
            installation).1.2.1.base.source.1.1 := by
    cases installation <;> exact hentryRight
  have eventualDrop (shift : Nat) :
      EventuallyStrictRight (fun k ↦ graphs (shift + k)) ∨
        EventuallyStrictLeft (fun k ↦ graphs (shift + k)) := by
    rcases heventual with hright | hleft
    · rcases hright with ⟨base, hbase⟩
      exact Or.inl ⟨base, fun n hn ↦ hbase (shift + n) (by omega)⟩
    · rcases hleft with ⟨base, hbase⟩
      exact Or.inr ⟨base, fun n hn ↦ hbase (shift + n) (by omega)⟩
  cases hgraphZero : graphs 0 with
  | both => exact False.elim (hnoboth 0 hgraphZero)
  | right =>
      by_cases hexists : ∃ close : Nat, graphs close ≠ .right
      · let close := Nat.find hexists
        have hcloseNe : graphs close ≠ .right := Nat.find_spec hexists
        have hbefore : ∀ k : Nat, k < close → graphs k = .right := by
          intro k hk
          by_contra hne
          exact (Nat.find_min hexists hk) hne
        have hclosePos : 0 < close := by
          by_contra hnot
          have hzero : close = 0 := by omega
          exact hcloseNe (by simpa [hzero] using hgraphZero)
        have hcloseLeft : graphs close = .left := by
          cases hcloseGraph : graphs close with
          | left => rfl
          | right => exact False.elim (hcloseNe hcloseGraph)
          | both => exact False.elim (hnoboth close hcloseGraph)
        let n := close - 1
        have hnclose : n + 1 = close := by
          dsimp only [n]
          omega
        have hright : ∀ k : Nat, k < n + 1 →
            (env (start + k)).graph = .right := by
          intro k hk
          exact hbefore k (by simpa [hnclose] using hk)
        have hclose : (env (start + (n + 1))).graph = .left := by
          simpa [graphs, hnclose] using hcloseLeft
        apply
          profiledRawJointHybridMegaGuarded_accepts_of_coupled_rightPrefix_leftClose_eventuallyFixed
            A strategy hwin controllers initialBank fallbackTag installation
              oldOutputOne oldOutputTwo env start n hphysical hentryRight
                hright hclose
        · intro k
          simpa [hnclose, Nat.add_assoc] using hnoboth (close + k)
        · simpa [graphs, hnclose, Nat.add_assoc] using eventualDrop close
      · have hall : ∀ k : Nat, (env (start + k)).graph = .right := by
          intro k
          by_contra hne
          exact hexists ⟨k, hne⟩
        exact profiledRawJointHybridMegaGuarded_accepts_of_coupled_allRight A
          strategy hwin controllers initialBank fallbackTag installation
            oldOutputOne oldOutputTwo env start hphysical hentryRight hall
  | left =>
      by_cases hexists : ∃ close : Nat, graphs close ≠ .left
      · let close := Nat.find hexists
        have hcloseNe : graphs close ≠ .left := Nat.find_spec hexists
        have hbefore : ∀ k : Nat, k < close → graphs k = .left := by
          intro k hk
          by_contra hne
          exact (Nat.find_min hexists hk) hne
        have hclosePos : 0 < close := by
          by_contra hnot
          have hzero : close = 0 := by omega
          exact hcloseNe (by simpa [hzero] using hgraphZero)
        have hcloseRight : graphs close = .right := by
          cases hcloseGraph : graphs close with
          | left => exact False.elim (hcloseNe hcloseGraph)
          | right => rfl
          | both => exact False.elim (hnoboth close hcloseGraph)
        let n := close - 1
        have hnclose : n + 1 = close := by
          dsimp only [n]
          omega
        have hleft : ∀ k : Nat, k < n + 1 →
            (env (start + k)).graph = .left := by
          intro k hk
          exact hbefore k (by simpa [hnclose] using hk)
        have hclose : (env (start + (n + 1))).graph = .right := by
          simpa [graphs, hnclose] using hcloseRight
        apply
          profiledRawJointHybridMegaGuarded_accepts_of_coupled_leftPrefix_rightClose_eventuallyFixed
            A strategy hwin controllers initialBank fallbackTag installation
              oldOutputOne oldOutputTwo env start n hphysical hentryLeft hleft
                hclose
        · intro k
          simpa [hnclose, Nat.add_assoc] using hnoboth (close + k)
        · simpa [graphs, hnclose, Nat.add_assoc] using eventualDrop close
      · have hall : ∀ k : Nat, (env (start + k)).graph = .left := by
          intro k
          by_contra hne
          exact hexists ⟨k, hne⟩
        exact profiledRawJointHybridMegaGuarded_accepts_of_coupled_allLeft A
          strategy hwin controllers initialBank fallbackTag installation
            oldOutputOne oldOutputTwo env start hphysical hentryLeft hall

end

end DetParityAutomaton

end DistributedSynthesis
