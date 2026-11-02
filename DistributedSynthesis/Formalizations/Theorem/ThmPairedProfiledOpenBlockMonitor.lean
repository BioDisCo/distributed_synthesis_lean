/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledBlockMonitor
import DistributedSynthesis.Formalizations.Theorem.ThmPairedEntryBranchFlatten

/-!
# Pre-policy profiled block monitors

The recurrent monitor used by the family construction must be installed
before choosing a rational transition policy.  Its successor condition is
therefore language nonemptiness of each exact profiled child, rather than
membership in one already selected policy.  This is the finite monitor on
which simultaneous hidden-root narrowing is sound.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

section

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

/-- A lambda is safe for the open right monitor when every exact child has a
rational accepting continuation. -/
def ProfiledOpenRightChildrenSafe
    (code : A.State × A.State)
    (lambda : ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) : Prop :=
  ∀ row past move,
    (pairedProfiledEntryRunAutomaton A
      (pairedProfiledOneChild A code lambda row past move)).HasRationalRun

/-- Left mirror. -/
def ProfiledOpenLeftChildrenSafe
    (code : A.State × A.State)
    (lambda : ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) : Prop :=
  ∀ row past move,
    (pairedProfiledEntryRunAutomaton A
      (pairedProfiledTwoChild A code lambda row past move)).HasRationalRun

/-- Right recurrent certificate monitor before an inner policy is selected. -/
noncomputable def profiledOpenRightBlockMonitor
    (code : A.State × A.State) (minimum : A.State)
    (profile : RightInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂)) :
    BlockRecordMonitor In₂ In₁ (ProfiledRightReceiverOutput A) Out₁ := by
  classical
  let U := (pairedRightThreadSystem A code).universalRunDPA
  exact {
    State := ProfiledRightBlockMonitorState A U.State
    stateFinite := inferInstance
    initial := (U.initial, pairedRightScanInitial A code, fun _ => none,
      true, true)
    step := fun state letter =>
      let physical := profiledRightPhysicalLetter A letter
      let rootMatches := !state.2.2.2.1 ||
        decide (pairedRightInformedForRow .first letter.2.1.physical =
          profile letter.1)
      let overlaps := ∀ row expected,
        state.2.2.1 row = some expected →
          pairedRightClosingForRow row letter.2.1.physical =
            expected (letter.1.2, letter.1.1)
      let targetsSafe := ∀ row,
        erasePairedProfiledState A (letter.2.1.target row) =
            pairedRightCloseTarget A state.2.1 row physical ∧
          (pairedProfiledEntryRunAutomaton A
            (letter.2.1.target row)).HasRationalRun
      (U.step state.1 physical,
        pairedRightScanStep A state.2.1 physical,
        fun row => leftProfileOfProfiledState A (letter.2.1.target row),
        false,
        state.2.2.2.2 && rootMatches && decide overlaps && decide targetsSafe)
    priority := fun state =>
      if state.2.2.2.2 then U.priority state.1 + 2 else 1
  }

/-- Left recurrent certificate monitor before an inner policy is selected. -/
noncomputable def profiledOpenLeftBlockMonitor
    (code : A.State × A.State) (minimum : A.State)
    (profile : LeftInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)) :
    BlockRecordMonitor In₁ In₂ (ProfiledLeftReceiverOutput A) Out₂ := by
  classical
  let U := (pairedLeftThreadSystem A code).universalRunDPA
  exact {
    State := ProfiledLeftBlockMonitorState A U.State
    stateFinite := inferInstance
    initial := (U.initial, pairedLeftScanInitial A code, fun _ => none,
      true, true)
    step := fun state letter =>
      let physical := profiledLeftPhysicalLetter A letter
      let rootMatches := !state.2.2.2.1 ||
        decide (pairedLeftInformedForRow .first letter.2.1.physical =
          profile letter.1)
      let overlaps := ∀ row expected,
        state.2.2.1 row = some expected →
          pairedLeftClosingForRow row letter.2.1.physical =
            expected (letter.1.2, letter.1.1)
      let targetsSafe := ∀ row,
        erasePairedProfiledState A (letter.2.1.target row) =
            pairedLeftCloseTarget A state.2.1 row physical ∧
          (pairedProfiledEntryRunAutomaton A
            (letter.2.1.target row)).HasRationalRun
      (U.step state.1 physical,
        pairedLeftScanStep A state.2.1 physical,
        fun row => rightProfileOfProfiledState A (letter.2.1.target row),
        false,
        state.2.2.2.2 && rootMatches && decide overlaps && decide targetsSafe)
    priority := fun state =>
      if state.2.2.2.2 then U.priority state.1 + 2 else 1
  }

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

/-- Exact run of the open right monitor on its semantic lambda. -/
theorem profiledOpenRightBlockMonitor_run_eq
    (code : A.State × A.State) (minimum : A.State)
    (profile : RightInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (lambda : ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hprofile : rightInitialFirstProfile lambda = profile)
    (hchildren : ProfiledOpenRightChildrenSafe A code lambda)
    (env : Nat → In₂ × In₁) : ∀ n,
      (profiledOpenRightBlockMonitor A code minimum profile).run
          (pairPlay (profiledRightReceiverStrategy A code lambda)
            (pairedRightSenderStrategy lambda) env) n =
        ((pairedRightThreadSystem A code).universalRunDPA.run
            (pairedRightBlockWord lambda env) n,
          pairedRightScanAfter A code lambda (omegaPrefix env n),
          profiledRightPendingAfter lambda (omegaPrefix env n),
          decide (n = 0), true) := by
  classical
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [BlockRecordMonitor.run, ih,
        profiledRight_pairPlay_eq_letterAt A code lambda env n,
        omegaPrefix_succ, pairedRightScanAfter_append,
        profiledRightPendingAfter_append]
      have hoverlaps : ∀ row expected,
          profiledRightPendingAfter lambda (omegaPrefix env n) row =
              some expected →
            pairedRightClosingForRow row
                (profiledRightReceiverStrategy A code lambda
                  (omegaPrefix env n) (env n)).physical =
              expected ((env n).2, (env n).1) :=
        profiledRightPendingAfter_realizes A code lambda
          (omegaPrefix env n) (env n)
      have htargets : ∀ row,
          erasePairedProfiledState A
              ((profiledRightReceiverStrategy A code lambda
                (omegaPrefix env n) (env n)).target row) =
              pairedRightCloseTarget A
                (pairedRightScanAfter A code lambda (omegaPrefix env n)) row
                (pairedRightBlockLetterAt lambda (omegaPrefix env n) (env n)) ∧
            (pairedProfiledEntryRunAutomaton A
              ((profiledRightReceiverStrategy A code lambda
                (omegaPrefix env n) (env n)).target row)).HasRationalRun := by
        intro row
        constructor
        · rw [profiledRightReceiverStrategy, erase_pairedProfiledOneChild,
            pairedRightCloseTarget_scanAfter]
        · exact hchildren row (omegaPrefix env n) (env n)
      have hphysicalAt :
          profiledRightPhysicalLetter A
              (env n,
                profiledRightReceiverStrategy A code lambda
                  (omegaPrefix env n) (env n),
                lambda.blind (senderWord (omegaPrefix env n)) (env n).2) =
            pairedRightBlockLetterAt lambda (omegaPrefix env n) (env n) := rfl
      simp only [profiledOpenRightBlockMonitor]
      rw [hphysicalAt, decide_eq_true hoverlaps, decide_eq_true htargets]
      rw [← pairedRightBlockWord_eq_letterAt lambda env n]
      by_cases hn : n = 0
      · subst n
        have hroot :
            pairedRightInformedForRow .first
                (pairedRightReceiverStrategy lambda [] (env 0)) =
              profile (env 0) := by
          simpa [rightInitialFirstProfile] using congrFun hprofile (env 0)
        simp [omegaPrefix, hroot, profiledRightTarget_profile]
      · simp [hn, profiledRightTarget_profile]

/-- Left mirror of `profiledOpenRightBlockMonitor_run_eq`. -/
theorem profiledOpenLeftBlockMonitor_run_eq
    (code : A.State × A.State) (minimum : A.State)
    (profile : LeftInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (lambda : ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hprofile : leftInitialFirstProfile lambda = profile)
    (hchildren : ProfiledOpenLeftChildrenSafe A code lambda)
    (env : Nat → In₁ × In₂) : ∀ n,
      (profiledOpenLeftBlockMonitor A code minimum profile).run
          (pairPlay (profiledLeftReceiverStrategy A code lambda)
            (pairedLeftSenderStrategy lambda) env) n =
        ((pairedLeftThreadSystem A code).universalRunDPA.run
            (pairedLeftBlockWord lambda env) n,
          pairedLeftScanAfter A code lambda (omegaPrefix env n),
          profiledLeftPendingAfter lambda (omegaPrefix env n),
          decide (n = 0), true) := by
  classical
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [BlockRecordMonitor.run, ih,
        profiledLeft_pairPlay_eq_letterAt A code lambda env n,
        omegaPrefix_succ, pairedLeftScanAfter_append,
        profiledLeftPendingAfter_append]
      have hoverlaps : ∀ row expected,
          profiledLeftPendingAfter lambda (omegaPrefix env n) row =
              some expected →
            pairedLeftClosingForRow row
                (profiledLeftReceiverStrategy A code lambda
                  (omegaPrefix env n) (env n)).physical =
              expected ((env n).2, (env n).1) :=
        profiledLeftPendingAfter_realizes A code lambda
          (omegaPrefix env n) (env n)
      have htargets : ∀ row,
          erasePairedProfiledState A
              ((profiledLeftReceiverStrategy A code lambda
                (omegaPrefix env n) (env n)).target row) =
              pairedLeftCloseTarget A
                (pairedLeftScanAfter A code lambda (omegaPrefix env n)) row
                (pairedLeftBlockLetterAt lambda (omegaPrefix env n) (env n)) ∧
            (pairedProfiledEntryRunAutomaton A
              ((profiledLeftReceiverStrategy A code lambda
                (omegaPrefix env n) (env n)).target row)).HasRationalRun := by
        intro row
        constructor
        · rw [profiledLeftReceiverStrategy, erase_pairedProfiledTwoChild,
            pairedLeftCloseTarget_scanAfter]
        · exact hchildren row (omegaPrefix env n) (env n)
      have hphysicalAt :
          profiledLeftPhysicalLetter A
              (env n,
                profiledLeftReceiverStrategy A code lambda
                  (omegaPrefix env n) (env n),
                lambda.blind (senderWord (omegaPrefix env n)) (env n).2) =
            pairedLeftBlockLetterAt lambda (omegaPrefix env n) (env n) := rfl
      simp only [profiledOpenLeftBlockMonitor]
      rw [hphysicalAt, decide_eq_true hoverlaps, decide_eq_true htargets]
      change
        ((pairedLeftThreadSystem A code).universalRunDPA.step
            ((pairedLeftThreadSystem A code).universalRunDPA.run
              (pairedLeftBlockWord lambda env) n)
            (pairedLeftBlockWord lambda env n), _, _, _, _) = _
      by_cases hn : n = 0
      · subst n
        have hroot :
            pairedLeftInformedForRow .first
                (pairedLeftReceiverStrategy lambda [] (env 0)) =
              profile (env 0) := by
          simpa [leftInitialFirstProfile] using congrFun hprofile (env 0)
        simp [omegaPrefix, hroot, profiledLeftTarget_profile]
      · simp [hn, profiledLeftTarget_profile]

/-- The original semantic right lambda realizes the open monitor. -/
theorem profiledOpenRightBlockMonitor_realizable
    (code : A.State × A.State) (minimum : A.State)
    (profile : RightInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (lambda : ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hforever : PairedRightForeverAccepts A code lambda)
    (hprofile : rightInitialFirstProfile lambda = profile)
    (hchildren : ProfiledOpenRightChildrenSafe A code lambda) :
    ∀ env : Nat → In₂ × In₁,
      (profiledOpenRightBlockMonitor A code minimum profile).WinsPlay
        (pairPlay (profiledRightReceiverStrategy A code lambda)
          (pairedRightSenderStrategy lambda) env) := by
  intro env
  have huniversal := pairedRightUniversalDPA_accepts_of_forever
    A code lambda hforever env
  have hshifted :=
    (natSeqMinEvenParity_add_const (d := 2) ⟨1, rfl⟩).mpr huniversal
  unfold BlockRecordMonitor.WinsPlay
  convert hshifted using 1
  funext n
  rw [profiledOpenRightBlockMonitor_run_eq A code minimum profile lambda
    hprofile hchildren env n]
  simp [profiledOpenRightBlockMonitor]
  rfl

/-- Left mirror. -/
theorem profiledOpenLeftBlockMonitor_realizable
    (code : A.State × A.State) (minimum : A.State)
    (profile : LeftInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (lambda : ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hforever : PairedLeftForeverAccepts A code lambda)
    (hprofile : leftInitialFirstProfile lambda = profile)
    (hchildren : ProfiledOpenLeftChildrenSafe A code lambda) :
    ∀ env : Nat → In₁ × In₂,
      (profiledOpenLeftBlockMonitor A code minimum profile).WinsPlay
        (pairPlay (profiledLeftReceiverStrategy A code lambda)
          (pairedLeftSenderStrategy lambda) env) := by
  intro env
  have huniversal := pairedLeftUniversalDPA_accepts_of_forever
    A code lambda hforever env
  have hshifted :=
    (natSeqMinEvenParity_add_const (d := 2) ⟨1, rfl⟩).mpr huniversal
  unfold BlockRecordMonitor.WinsPlay
  convert hshifted using 1
  funext n
  rw [profiledOpenLeftBlockMonitor_run_eq A code minimum profile lambda
    hprofile hchildren env n]
  simp [profiledOpenLeftBlockMonitor]
  rfl

end

/-! ## Discharge from the original winning strategy -/

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Every exact right child produced by the raw winning strategy has an
accepting rational continuation.  The only imported ingredient is the
classical rational-run basis for that finite-state parity tree automaton. -/
theorem profiledOpenRightChildrenSafe_of_winning
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : ProcOnePairedEntryRep strategy) (minimum : A.State)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis) :
    ProfiledOpenRightChildrenSafe A entry.code entry.lambdaOfStrategy := by
  intro row past move
  let memory : PairedStrategyMemory A strategy := .processOne entry minimum
  let direction : PairedEntryDirection (In₁ := In₁) (In₂ := In₂) :=
    .fromOne row past move
  let child := memory.step (A := A) direction
  have hrat : (pairedProfiledEntryRunAutomaton A
      (PairedStrategyMemory.toProfiledTreeState (A := A) child)).HasRationalRun :=
    child.profiledHasRationalRun (A := A)
      (basis (PairedStrategyMemory.toProfiledTreeState (A := A) child))
      (child.foreverAccepts_of_winning (A := A) hwin)
      (PairedStrategyMemory.switchingAccepts_of_winning hwin child)
  have hstate : PairedStrategyMemory.toProfiledTreeState (A := A) child =
      pairedProfiledOneChild A entry.code entry.lambdaOfStrategy row past move := by
    simpa [child, direction, memory] using
      (PairedStrategyMemory.toProfiledTreeState_step (A := A) memory direction)
  simpa [hstate] using hrat

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Left mirror. -/
theorem profiledOpenLeftChildrenSafe_of_winning
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : ProcTwoPairedEntryRep strategy) (minimum : A.State)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis) :
    ProfiledOpenLeftChildrenSafe A entry.code entry.lambdaOfStrategy := by
  intro row past move
  let memory : PairedStrategyMemory A strategy := .processTwo entry minimum
  let direction : PairedEntryDirection (In₁ := In₁) (In₂ := In₂) :=
    .fromTwo row past move
  let child := memory.step (A := A) direction
  have hrat : (pairedProfiledEntryRunAutomaton A
      (PairedStrategyMemory.toProfiledTreeState (A := A) child)).HasRationalRun :=
    child.profiledHasRationalRun (A := A)
      (basis (PairedStrategyMemory.toProfiledTreeState (A := A) child))
      (child.foreverAccepts_of_winning (A := A) hwin)
      (PairedStrategyMemory.switchingAccepts_of_winning hwin child)
  have hstate : PairedStrategyMemory.toProfiledTreeState (A := A) child =
      pairedProfiledTwoChild A entry.code entry.lambdaOfStrategy row past move := by
    simpa [child, direction, memory] using
      (PairedStrategyMemory.toProfiledTreeState_step (A := A) memory direction)
  simpa [hstate] using hrat

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The raw strategy at a process-one paired entry realizes the correct
pre-policy monitor.  No selected inner lambda occurs in the statement. -/
theorem profiledOpenRightBlockMonitor_realizable_of_winning
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : ProcOnePairedEntryRep strategy) (minimum : A.State)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis) :
    ∀ env : Nat → In₂ × In₁,
      (profiledOpenRightBlockMonitor A entry.code minimum
        (rightInitialFirstProfile entry.lambdaOfStrategy)).WinsPlay
        (pairPlay
          (profiledRightReceiverStrategy A entry.code entry.lambdaOfStrategy)
          (pairedRightSenderStrategy entry.lambdaOfStrategy) env) := by
  let memory : PairedStrategyMemory A strategy := .processOne entry minimum
  apply profiledOpenRightBlockMonitor_realizable A entry.code minimum
    (rightInitialFirstProfile entry.lambdaOfStrategy) entry.lambdaOfStrategy
  · simpa [memory, PairedStrategyMemory.ForeverAccepts] using
      (memory.foreverAccepts_of_winning (A := A) hwin [])
  · rfl
  · exact profiledOpenRightChildrenSafe_of_winning A strategy hwin entry
      minimum basis

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Process-two mirror. -/
theorem profiledOpenLeftBlockMonitor_realizable_of_winning
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : ProcTwoPairedEntryRep strategy) (minimum : A.State)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis) :
    ∀ env : Nat → In₁ × In₂,
      (profiledOpenLeftBlockMonitor A entry.code minimum
        (leftInitialFirstProfile entry.lambdaOfStrategy)).WinsPlay
        (pairPlay
          (profiledLeftReceiverStrategy A entry.code entry.lambdaOfStrategy)
          (pairedLeftSenderStrategy entry.lambdaOfStrategy) env) := by
  let memory : PairedStrategyMemory A strategy := .processTwo entry minimum
  apply profiledOpenLeftBlockMonitor_realizable A entry.code minimum
    (leftInitialFirstProfile entry.lambdaOfStrategy) entry.lambdaOfStrategy
  · simpa [memory, PairedStrategyMemory.ForeverAccepts] using
      (memory.foreverAccepts_of_winning (A := A) hwin [])
  · rfl
  · exact profiledOpenLeftChildrenSafe_of_winning A strategy hwin entry
      minimum basis

end

end

end DetParityAutomaton

end DistributedSynthesis
