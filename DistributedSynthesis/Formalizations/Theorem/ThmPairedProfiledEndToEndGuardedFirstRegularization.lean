/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndGuardedPolicy

/-!
# One-policy regularization of the guarded first recurrent block

These sticky monitors strengthen the earlier guarded-first monitors.  An
emitted profiled child must be an actual successor of the single guarded
policy supplied by the initial common-policy construction.  Mere existence
of an unrelated rational run is no longer sufficient.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

set_option synthInstance.maxHeartbeats 300000

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

/-! ## Process-one / first-right orientation -/

/-- Guarded first-right monitor tied to one supplied rational policy. -/
noncomputable def endToEndGuardedFirstRightBlockMonitor
    (target : PairedProfiledTreeState A)
    (overlap : ProcOneEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (policy : (rightProfiledGuardedAutomaton A target overlap).RationalTransitionPolicy)
    (code : A.State × A.State) (minimum : A.State)
    (initialProfile : RightInitialActionProfile
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
      let guardedRootOK := !state.2.2.2.1 ||
        decide (overlap letter.1 = letter.2.1.physical.closingFirst)
      let profiledRootOK := !state.2.2.2.1 ||
        decide (pairedRightInformedForRow .first letter.2.1.physical =
          initialProfile letter.1)
      let overlaps := ∀ row expected,
        state.2.2.1 row = some expected →
          pairedRightClosingForRow row letter.2.1.physical =
            expected (letter.1.2, letter.1.1)
      let targetsSafe := ∀ row,
        erasePairedProfiledState A (letter.2.1.target row) =
            pairedRightCloseTarget A state.2.1 row physical ∧
          ProfiledGuardedRightPolicyAllows A target overlap policy
            (letter.2.1.target row)
      (U.step state.1 physical,
        pairedRightScanStep A state.2.1 physical,
        fun row => leftProfileOfProfiledState A (letter.2.1.target row),
        false,
        state.2.2.2.2 && guardedRootOK && profiledRootOK &&
          decide overlaps && decide targetsSafe)
    priority := fun state =>
      if state.2.2.2.2 then U.priority state.1 + 2 else 1
  }

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- The raw lambda read from the supplied policy realizes the strengthened
monitor. -/
theorem endToEndGuardedFirstRightBlockMonitor_run_eq
    (target : PairedProfiledTreeState A)
    (overlap : ProcOneEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (policy : (rightProfiledGuardedAutomaton A target overlap).RationalTransitionPolicy)
    (code : A.State × A.State) (minimum : A.State)
    (initialProfile : RightInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (activation : EndToEndGuardedRightActivation A target overlap policy code
      minimum initialProfile)
    (env : Nat → In₂ × In₁) : ∀ n,
    (endToEndGuardedFirstRightBlockMonitor A target overlap policy code minimum
        initialProfile).run
        (pairPlay (profiledRightReceiverStrategy A code activation.lambda)
          (pairedRightSenderStrategy activation.lambda) env) n =
      ((pairedRightThreadSystem A code).universalRunDPA.run
          (pairedRightBlockWord activation.lambda env) n,
        pairedRightScanAfter A code activation.lambda (omegaPrefix env n),
        profiledRightPendingAfter activation.lambda (omegaPrefix env n),
        decide (n = 0), true) := by
  classical
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [BlockRecordMonitor.run, ih,
        profiledRight_pairPlay_eq_letterAt A code activation.lambda env n,
        omegaPrefix_succ, pairedRightScanAfter_append,
        profiledRightPendingAfter_append]
      have hoverlaps := profiledRightPendingAfter_realizes A code
        activation.lambda (omegaPrefix env n) (env n)
      have htargets : ∀ row,
          erasePairedProfiledState A
              ((profiledRightReceiverStrategy A code activation.lambda
                (omegaPrefix env n) (env n)).target row) =
              pairedRightCloseTarget A
                (pairedRightScanAfter A code activation.lambda
                  (omegaPrefix env n)) row
                (pairedRightBlockLetterAt activation.lambda
                  (omegaPrefix env n) (env n)) ∧
            ProfiledGuardedRightPolicyAllows A target overlap policy
              ((profiledRightReceiverStrategy A code activation.lambda
                (omegaPrefix env n) (env n)).target row) := by
        intro row
        constructor
        · rw [profiledRightReceiverStrategy, erase_pairedProfiledOneChild,
            pairedRightCloseTarget_scanAfter]
        · exact activation.childAllowed row (omegaPrefix env n) (env n)
      have hguarded :
          (!decide (n = 0) || decide
            (overlap (env n) =
              (profiledRightReceiverStrategy A code activation.lambda
                (omegaPrefix env n) (env n)).physical.closingFirst)) = true := by
        cases n with
        | zero =>
            have hm := activation.overlap_matches (env 0)
            simp [ProcOneEntryOverlapProfile.Matches,
              profiledRightReceiverStrategy, pairedRightReceiverStrategy] at hm ⊢
            exact hm.symm
        | succ n => rfl
      have hprofiled :
          (!decide (n = 0) || decide
            (pairedRightInformedForRow .first
                (profiledRightReceiverStrategy A code activation.lambda
                  (omegaPrefix env n) (env n)).physical =
              initialProfile (env n))) = true := by
        cases n with
        | zero =>
            have hp := congrFun activation.initial_profile (env 0)
            simp [rightInitialFirstProfile] at hp
            simpa using hp
        | succ n => rfl
      have hphysicalAt :
          profiledRightPhysicalLetter A
              (env n,
                profiledRightReceiverStrategy A code activation.lambda
                  (omegaPrefix env n) (env n),
                activation.lambda.blind
                  (senderWord (omegaPrefix env n)) (env n).2) =
            pairedRightBlockLetterAt activation.lambda
              (omegaPrefix env n) (env n) := rfl
      simp only [endToEndGuardedFirstRightBlockMonitor]
      rw [hphysicalAt, hguarded, hprofiled,
        decide_eq_true hoverlaps, decide_eq_true htargets]
      rw [← pairedRightBlockWord_eq_letterAt activation.lambda env n]
      simp [profiledRightTarget_profile]

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem endToEndGuardedFirstRightBlockMonitor_realizable
    (target : PairedProfiledTreeState A)
    (overlap : ProcOneEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (policy : (rightProfiledGuardedAutomaton A target overlap).RationalTransitionPolicy)
    (code : A.State × A.State) (minimum : A.State)
    (initialProfile : RightInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (activation : EndToEndGuardedRightActivation A target overlap policy code
      minimum initialProfile) :
    ∀ env : Nat → In₂ × In₁,
      (endToEndGuardedFirstRightBlockMonitor A target overlap policy code minimum
        initialProfile).WinsPlay
        (pairPlay (profiledRightReceiverStrategy A code activation.lambda)
          (pairedRightSenderStrategy activation.lambda) env) := by
  intro env
  have huniversal := pairedRightUniversalDPA_accepts_of_forever A code
    activation.lambda activation.forever env
  unfold BlockRecordMonitor.WinsPlay
  have hshifted := (natSeqMinEvenParity_add_const (d := 2) ⟨1, rfl⟩).mpr
    huniversal
  convert hshifted using 1
  funext n
  rw [endToEndGuardedFirstRightBlockMonitor_run_eq A target overlap policy code
    minimum initialProfile activation env n]
  rfl

/-- Unconditional finite controller whose emitted children all belong to the
same supplied guarded policy. -/
theorem exists_finite_endToEndGuardedFirstRightController
    (target : PairedProfiledTreeState A)
    (overlap : ProcOneEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (policy : (rightProfiledGuardedAutomaton A target overlap).RationalTransitionPolicy)
    (code : A.State × A.State) (minimum : A.State)
    (initialProfile : RightInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (hshape : target = .inr (.inl ((code, minimum), initialProfile))) :
    ∃ controller : TransitionRationalTree.{u, max 1 u v x y s, max 1 s u v x}
      In₁ (NarrowedBlockLabel In₂ In₁ (ProfiledRightReceiverOutput A) Out₁
        (endToEndGuardedFirstRightBlockMonitor.{u, v, x, y, s, 1}
          A target overlap policy code minimum initialProfile).State),
      NarrowedAllThreadsWin
        (endToEndGuardedFirstRightBlockMonitor.{u, v, x, y, s, 1}
          A target overlap policy code minimum initialProfile)
        controller.labeledTree := by
  let activation := endToEndGuardedRightActivation A target overlap policy code
    minimum initialProfile hshape
  refine (block_realizable_iff_implementable_controller_unconditional
    (endToEndGuardedFirstRightBlockMonitor.{u, v, x, y, s, 1}
      A target overlap policy code minimum initialProfile)).mp ?_
  exact ⟨profiledRightReceiverStrategy A code activation.lambda,
    pairedRightSenderStrategy activation.lambda,
    endToEndGuardedFirstRightBlockMonitor_realizable A target overlap policy
      code minimum initialProfile activation⟩

/-! ## Process-two / first-left orientation -/

/-- Guarded first-left monitor tied to one supplied rational policy. -/
noncomputable def endToEndGuardedFirstLeftBlockMonitor
    (target : PairedProfiledTreeState A)
    (overlap : ProcTwoEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (policy : (leftProfiledGuardedAutomaton A target overlap).RationalTransitionPolicy)
    (code : A.State × A.State) (minimum : A.State)
    (initialProfile : LeftInitialActionProfile
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
      let guardedRootOK := !state.2.2.2.1 ||
        decide (overlap letter.1 = letter.2.1.physical.closingFirst)
      let profiledRootOK := !state.2.2.2.1 ||
        decide (pairedLeftInformedForRow .first letter.2.1.physical =
          initialProfile letter.1)
      let overlaps := ∀ row expected,
        state.2.2.1 row = some expected →
          pairedLeftClosingForRow row letter.2.1.physical =
            expected (letter.1.2, letter.1.1)
      let targetsSafe := ∀ row,
        erasePairedProfiledState A (letter.2.1.target row) =
            pairedLeftCloseTarget A state.2.1 row physical ∧
          ProfiledGuardedLeftPolicyAllows A target overlap policy
            (letter.2.1.target row)
      (U.step state.1 physical,
        pairedLeftScanStep A state.2.1 physical,
        fun row => rightProfileOfProfiledState A (letter.2.1.target row),
        false,
        state.2.2.2.2 && guardedRootOK && profiledRootOK &&
          decide overlaps && decide targetsSafe)
    priority := fun state =>
      if state.2.2.2.2 then U.priority state.1 + 2 else 1
  }

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem endToEndGuardedFirstLeftBlockMonitor_run_eq
    (target : PairedProfiledTreeState A)
    (overlap : ProcTwoEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (policy : (leftProfiledGuardedAutomaton A target overlap).RationalTransitionPolicy)
    (code : A.State × A.State) (minimum : A.State)
    (initialProfile : LeftInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (activation : EndToEndGuardedLeftActivation A target overlap policy code
      minimum initialProfile)
    (env : Nat → In₁ × In₂) : ∀ n,
    (endToEndGuardedFirstLeftBlockMonitor A target overlap policy code minimum
        initialProfile).run
        (pairPlay (profiledLeftReceiverStrategy A code activation.lambda)
          (pairedLeftSenderStrategy activation.lambda) env) n =
      ((pairedLeftThreadSystem A code).universalRunDPA.run
          (pairedLeftBlockWord activation.lambda env) n,
        pairedLeftScanAfter A code activation.lambda (omegaPrefix env n),
        profiledLeftPendingAfter activation.lambda (omegaPrefix env n),
        decide (n = 0), true) := by
  classical
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [BlockRecordMonitor.run, ih,
        profiledLeft_pairPlay_eq_letterAt A code activation.lambda env n,
        omegaPrefix_succ, pairedLeftScanAfter_append,
        profiledLeftPendingAfter_append]
      have hoverlaps := profiledLeftPendingAfter_realizes A code
        activation.lambda (omegaPrefix env n) (env n)
      have htargets : ∀ row,
          erasePairedProfiledState A
              ((profiledLeftReceiverStrategy A code activation.lambda
                (omegaPrefix env n) (env n)).target row) =
              pairedLeftCloseTarget A
                (pairedLeftScanAfter A code activation.lambda
                  (omegaPrefix env n)) row
                (pairedLeftBlockLetterAt activation.lambda
                  (omegaPrefix env n) (env n)) ∧
            ProfiledGuardedLeftPolicyAllows A target overlap policy
              ((profiledLeftReceiverStrategy A code activation.lambda
                (omegaPrefix env n) (env n)).target row) := by
        intro row
        constructor
        · rw [profiledLeftReceiverStrategy, erase_pairedProfiledTwoChild,
            pairedLeftCloseTarget_scanAfter]
        · exact activation.childAllowed row (omegaPrefix env n) (env n)
      have hguarded :
          (!decide (n = 0) || decide
            (overlap (env n) =
              (profiledLeftReceiverStrategy A code activation.lambda
                (omegaPrefix env n) (env n)).physical.closingFirst)) = true := by
        cases n with
        | zero =>
            have hm := activation.overlap_matches (env 0)
            simp [profiledLeftReceiverStrategy,
              pairedLeftReceiverStrategy] at hm ⊢
            exact hm.symm
        | succ n => rfl
      have hprofiled :
          (!decide (n = 0) || decide
            (pairedLeftInformedForRow .first
                (profiledLeftReceiverStrategy A code activation.lambda
                  (omegaPrefix env n) (env n)).physical =
              initialProfile (env n))) = true := by
        cases n with
        | zero =>
            have hp := congrFun activation.initial_profile (env 0)
            simp [leftInitialFirstProfile] at hp
            simpa using hp
        | succ n => rfl
      have hphysicalAt :
          profiledLeftPhysicalLetter A
              (env n,
                profiledLeftReceiverStrategy A code activation.lambda
                  (omegaPrefix env n) (env n),
                activation.lambda.blind
                  (senderWord (omegaPrefix env n)) (env n).2) =
            pairedLeftBlockLetterAt activation.lambda
              (omegaPrefix env n) (env n) := rfl
      simp only [endToEndGuardedFirstLeftBlockMonitor]
      rw [hphysicalAt, hguarded, hprofiled,
        decide_eq_true hoverlaps, decide_eq_true htargets]
      change
        ((pairedLeftThreadSystem A code).universalRunDPA.step
            ((pairedLeftThreadSystem A code).universalRunDPA.run
              (pairedLeftBlockWord activation.lambda env) n)
            (pairedLeftBlockWord activation.lambda env n), _, _, _, _) = _
      simp [profiledLeftTarget_profile]

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem endToEndGuardedFirstLeftBlockMonitor_realizable
    (target : PairedProfiledTreeState A)
    (overlap : ProcTwoEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (policy : (leftProfiledGuardedAutomaton A target overlap).RationalTransitionPolicy)
    (code : A.State × A.State) (minimum : A.State)
    (initialProfile : LeftInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (activation : EndToEndGuardedLeftActivation A target overlap policy code
      minimum initialProfile) :
    ∀ env : Nat → In₁ × In₂,
      (endToEndGuardedFirstLeftBlockMonitor A target overlap policy code minimum
        initialProfile).WinsPlay
        (pairPlay (profiledLeftReceiverStrategy A code activation.lambda)
          (pairedLeftSenderStrategy activation.lambda) env) := by
  intro env
  have huniversal := pairedLeftUniversalDPA_accepts_of_forever A code
    activation.lambda activation.forever env
  unfold BlockRecordMonitor.WinsPlay
  have hshifted := (natSeqMinEvenParity_add_const (d := 2) ⟨1, rfl⟩).mpr
    huniversal
  convert hshifted using 1
  funext n
  rw [endToEndGuardedFirstLeftBlockMonitor_run_eq A target overlap policy code
    minimum initialProfile activation env n]
  rfl

/-- Left mirror: unconditional finite controller with common-policy
successor targets. -/
theorem exists_finite_endToEndGuardedFirstLeftController
    (target : PairedProfiledTreeState A)
    (overlap : ProcTwoEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (policy : (leftProfiledGuardedAutomaton A target overlap).RationalTransitionPolicy)
    (code : A.State × A.State) (minimum : A.State)
    (initialProfile : LeftInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (hshape : target = .inr (.inr ((code, minimum), initialProfile))) :
    ∃ controller : TransitionRationalTree.{v, max 1 u v x y s, max 1 s u v y}
      In₂ (NarrowedBlockLabel In₁ In₂ (ProfiledLeftReceiverOutput A) Out₂
        (endToEndGuardedFirstLeftBlockMonitor.{u, v, x, y, s, 1}
          A target overlap policy code minimum initialProfile).State),
      NarrowedAllThreadsWin
        (endToEndGuardedFirstLeftBlockMonitor.{u, v, x, y, s, 1}
          A target overlap policy code minimum initialProfile)
        controller.labeledTree := by
  let activation := endToEndGuardedLeftActivation A target overlap policy code
    minimum initialProfile hshape
  refine (block_realizable_iff_implementable_controller_unconditional
    (endToEndGuardedFirstLeftBlockMonitor.{u, v, x, y, s, 1}
      A target overlap policy code minimum initialProfile)).mp ?_
  exact ⟨profiledLeftReceiverStrategy A code activation.lambda,
    pairedLeftSenderStrategy activation.lambda,
    endToEndGuardedFirstLeftBlockMonitor_realizable A target overlap policy
      code minimum initialProfile activation⟩

end


end DetParityAutomaton

end DistributedSynthesis
