/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledGuardedHandoff
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledBlockMonitor

/-!
# Finite regularization of the profiled guarded first block

The exceptional first recurrent block must preserve two independent finite
boundary promises: the one-shot overlap inherited from the initial phase and
the recurrent action profile stored in the profiled tree state.  Its receiver
also emits the exact profiled child for each latent close row.

The sticky monitor below checks both root promises, the delayed overlap between
successive block letters, the erased DPA close target, and rational-run
nonemptiness of every emitted child.  Consequently a narrowed finite
controller hands off directly to `FeasibleProfiledPairedState`; it never
forgets the profile by passing through the older ordinary bank.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

set_option synthInstance.maxHeartbeats 300000

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

section

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

/-! ## Semantic guarded activations -/

/-- Semantic payload selected at a profiled guarded right root. -/
structure ProfiledGuardedRightActivation
    (source : ProfiledGuardedRightEntrySource A)
    (code : A.State × A.State) (minimum : A.State)
    (initialProfile : RightInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂)) where
  lambda : ProcOnePairedRightLambda
    (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
  overlap_matches : source.1.2.Matches lambda
  forever : PairedRightForeverAccepts A code lambda
  initial_profile : rightInitialFirstProfile lambda = initialProfile
  childFeasible : ∀ row past move,
    (pairedProfiledEntryRunAutomaton A
      (pairedProfiledOneChild A code lambda row past move)).HasRationalRun

/-- Select the complete right activation from the guarded rational policy. -/
noncomputable def profiledGuardedRightActivation
    (source : ProfiledGuardedRightEntrySource A)
    (code : A.State × A.State) (minimum : A.State)
    (initialProfile : RightInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (hshape : source.1.1 = .inr (.inl ((code, minimum), initialProfile))) :
    ProfiledGuardedRightActivation A source code minimum initialProfile := by
  classical
  let hexists := profiledGuardedRightEntryPolicy_root A source code minimum
    initialProfile hshape
  let lambda := Classical.choose hexists
  have hspec := Classical.choose_spec hexists
  exact {
    lambda := lambda
    overlap_matches := hspec.1
    forever := hspec.2.1
    initial_profile := hspec.2.2.1
    childFeasible := fun row past move =>
      profiledGuardedRightEntry_child_hasRationalRun A source code minimum
        initialProfile lambda hspec.2.2.2 row past move
  }

/-- Semantic payload selected at a profiled guarded left root. -/
structure ProfiledGuardedLeftActivation
    (source : ProfiledGuardedLeftEntrySource A)
    (code : A.State × A.State) (minimum : A.State)
    (initialProfile : LeftInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)) where
  lambda : ProcTwoPairedLeftLambda
    (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
  overlap_matches : source.1.2.Matches lambda
  forever : PairedLeftForeverAccepts A code lambda
  initial_profile : leftInitialFirstProfile lambda = initialProfile
  childFeasible : ∀ row past move,
    (pairedProfiledEntryRunAutomaton A
      (pairedProfiledTwoChild A code lambda row past move)).HasRationalRun

/-- Select the complete left activation from the guarded rational policy. -/
noncomputable def profiledGuardedLeftActivation
    (source : ProfiledGuardedLeftEntrySource A)
    (code : A.State × A.State) (minimum : A.State)
    (initialProfile : LeftInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (hshape : source.1.1 = .inr (.inr ((code, minimum), initialProfile))) :
    ProfiledGuardedLeftActivation A source code minimum initialProfile := by
  classical
  let hexists := profiledGuardedLeftEntryPolicy_root A source code minimum
    initialProfile hshape
  let lambda := Classical.choose hexists
  have hspec := Classical.choose_spec hexists
  exact {
    lambda := lambda
    overlap_matches := hspec.1
    forever := hspec.2.1
    initial_profile := hspec.2.2.1
    childFeasible := fun row past move =>
      profiledGuardedLeftEntry_child_hasRationalRun A source code minimum
        initialProfile lambda hspec.2.2.2 row past move
  }

/-! ## Sticky certificate monitors -/

/-- Profiled exceptional right-block monitor. -/
noncomputable def profiledGuardedFirstRightBlockMonitor
    (source : ProfiledGuardedRightEntrySource A)
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
        decide (source.1.2 letter.1 = letter.2.1.physical.closingFirst)
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
          (pairedProfiledEntryRunAutomaton A
            (letter.2.1.target row)).HasRationalRun
      (U.step state.1 physical,
        pairedRightScanStep A state.2.1 physical,
        fun row => leftProfileOfProfiledState A (letter.2.1.target row),
        false,
        state.2.2.2.2 && guardedRootOK && profiledRootOK &&
          decide overlaps && decide targetsSafe)
    priority := fun state =>
      if state.2.2.2.2 then U.priority state.1 + 2 else 1
  }

/-- Profiled exceptional left-block monitor. -/
noncomputable def profiledGuardedFirstLeftBlockMonitor
    (source : ProfiledGuardedLeftEntrySource A)
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
        decide (source.1.2 letter.1 = letter.2.1.physical.closingFirst)
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
          (pairedProfiledEntryRunAutomaton A
            (letter.2.1.target row)).HasRationalRun
      (U.step state.1 physical,
        pairedLeftScanStep A state.2.1 physical,
        fun row => rightProfileOfProfiledState A (letter.2.1.target row),
        false,
        state.2.2.2.2 && guardedRootOK && profiledRootOK &&
          decide overlaps && decide targetsSafe)
    priority := fun state =>
      if state.2.2.2.2 then U.priority state.1 + 2 else 1
  }

/-! ## Exact semantic runs -/

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledGuardedFirstRightBlockMonitor_run_eq
    (source : ProfiledGuardedRightEntrySource A)
    (code : A.State × A.State) (minimum : A.State)
    (initialProfile : RightInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (activation : ProfiledGuardedRightActivation A source code minimum
      initialProfile)
    (env : Nat → In₂ × In₁) : ∀ n,
    (profiledGuardedFirstRightBlockMonitor A source code minimum
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
            (pairedProfiledEntryRunAutomaton A
              ((profiledRightReceiverStrategy A code activation.lambda
                (omegaPrefix env n) (env n)).target row)).HasRationalRun := by
        intro row
        constructor
        · rw [profiledRightReceiverStrategy, erase_pairedProfiledOneChild,
            pairedRightCloseTarget_scanAfter]
        · exact activation.childFeasible row (omegaPrefix env n) (env n)
      have hguarded :
          (!decide (n = 0) || decide
            (source.1.2 (env n) =
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
      simp only [profiledGuardedFirstRightBlockMonitor]
      rw [hphysicalAt, hguarded, hprofiled,
        decide_eq_true hoverlaps, decide_eq_true htargets]
      rw [← pairedRightBlockWord_eq_letterAt activation.lambda env n]
      simp [profiledRightTarget_profile]

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledGuardedFirstRightBlockMonitor_realizable
    (source : ProfiledGuardedRightEntrySource A)
    (code : A.State × A.State) (minimum : A.State)
    (initialProfile : RightInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (activation : ProfiledGuardedRightActivation A source code minimum
      initialProfile) :
    ∀ env : Nat → In₂ × In₁,
      (profiledGuardedFirstRightBlockMonitor A source code minimum
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
  rw [profiledGuardedFirstRightBlockMonitor_run_eq A source code minimum
    initialProfile activation env n]
  rfl

/-- Unconditional finite controller for the profiled guarded first-right block. -/
theorem exists_finite_profiledGuardedFirstRightController
    (source : ProfiledGuardedRightEntrySource A)
    (code : A.State × A.State) (minimum : A.State)
    (initialProfile : RightInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (hshape : source.1.1 = .inr (.inl ((code, minimum), initialProfile))) :
    ∃ controller : TransitionRationalTree.{u, max 1 u v x y s, max 1 s u v x}
      In₁ (NarrowedBlockLabel In₂ In₁ (ProfiledRightReceiverOutput A) Out₁
        (profiledGuardedFirstRightBlockMonitor.{u, v, x, y, s, 1}
          A source code minimum initialProfile).State),
      NarrowedAllThreadsWin
        (profiledGuardedFirstRightBlockMonitor.{u, v, x, y, s, 1}
          A source code minimum initialProfile) controller.labeledTree := by
  let activation := profiledGuardedRightActivation A source code minimum
    initialProfile hshape
  refine (block_realizable_iff_implementable_controller_unconditional
    (profiledGuardedFirstRightBlockMonitor.{u, v, x, y, s, 1}
      A source code minimum initialProfile)).mp ?_
  exact ⟨profiledRightReceiverStrategy A code activation.lambda,
    pairedRightSenderStrategy activation.lambda,
    profiledGuardedFirstRightBlockMonitor_realizable A source code minimum
      initialProfile activation⟩

/-! ### Left mirror -/

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledGuardedFirstLeftBlockMonitor_run_eq
    (source : ProfiledGuardedLeftEntrySource A)
    (code : A.State × A.State) (minimum : A.State)
    (initialProfile : LeftInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (activation : ProfiledGuardedLeftActivation A source code minimum
      initialProfile)
    (env : Nat → In₁ × In₂) : ∀ n,
    (profiledGuardedFirstLeftBlockMonitor A source code minimum
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
            (pairedProfiledEntryRunAutomaton A
              ((profiledLeftReceiverStrategy A code activation.lambda
                (omegaPrefix env n) (env n)).target row)).HasRationalRun := by
        intro row
        constructor
        · rw [profiledLeftReceiverStrategy, erase_pairedProfiledTwoChild,
            pairedLeftCloseTarget_scanAfter]
        · exact activation.childFeasible row (omegaPrefix env n) (env n)
      have hguarded :
          (!decide (n = 0) || decide
            (source.1.2 (env n) =
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
      simp only [profiledGuardedFirstLeftBlockMonitor]
      rw [hphysicalAt, hguarded, hprofiled,
        decide_eq_true hoverlaps, decide_eq_true htargets]
      change
        ((pairedLeftThreadSystem A code).universalRunDPA.step
            ((pairedLeftThreadSystem A code).universalRunDPA.run
              (pairedLeftBlockWord activation.lambda env) n)
            (pairedLeftBlockWord activation.lambda env n), _, _, _, _) = _
      simp [profiledLeftTarget_profile]

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledGuardedFirstLeftBlockMonitor_realizable
    (source : ProfiledGuardedLeftEntrySource A)
    (code : A.State × A.State) (minimum : A.State)
    (initialProfile : LeftInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (activation : ProfiledGuardedLeftActivation A source code minimum
      initialProfile) :
    ∀ env : Nat → In₁ × In₂,
      (profiledGuardedFirstLeftBlockMonitor A source code minimum
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
  rw [profiledGuardedFirstLeftBlockMonitor_run_eq A source code minimum
    initialProfile activation env n]
  rfl

/-- Unconditional finite controller for the profiled guarded first-left block. -/
theorem exists_finite_profiledGuardedFirstLeftController
    (source : ProfiledGuardedLeftEntrySource A)
    (code : A.State × A.State) (minimum : A.State)
    (initialProfile : LeftInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (hshape : source.1.1 = .inr (.inr ((code, minimum), initialProfile))) :
    ∃ controller : TransitionRationalTree.{v, max 1 u v x y s, max 1 s u v y}
      In₂ (NarrowedBlockLabel In₁ In₂ (ProfiledLeftReceiverOutput A) Out₂
        (profiledGuardedFirstLeftBlockMonitor.{u, v, x, y, s, 1}
          A source code minimum initialProfile).State),
      NarrowedAllThreadsWin
        (profiledGuardedFirstLeftBlockMonitor.{u, v, x, y, s, 1}
          A source code minimum initialProfile) controller.labeledTree := by
  let activation := profiledGuardedLeftActivation A source code minimum
    initialProfile hshape
  refine (block_realizable_iff_implementable_controller_unconditional
    (profiledGuardedFirstLeftBlockMonitor.{u, v, x, y, s, 1}
      A source code minimum initialProfile)).mp ?_
  exact ⟨profiledLeftReceiverStrategy A code activation.lambda,
    pairedLeftSenderStrategy activation.lambda,
    profiledGuardedFirstLeftBlockMonitor_realizable A source code minimum
      initialProfile activation⟩

end

end


end DetParityAutomaton

end DistributedSynthesis
