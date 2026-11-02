/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedGuardedPolicyActivation
import DistributedSynthesis.Formalizations.Theorem.ThmPairedEntryBlockRegularization

/-!
# Finite regularization of the guarded first recurrent block

The first recurrent block is exceptional only at its root.  Its finite monitor
checks the promised overlap profile on the first letter, checks ordinary-bank
feasibility for both possible close rows on every letter, and otherwise uses
the existing universal two-thread parity monitor.  Thus sender narrowing can
make this block finite-state without losing the one-shot handoff guarantee.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

set_option synthInstance.maxHeartbeats 200000

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

/-- Monitor for the one exceptional right block immediately following an
initial-left boundary. -/
noncomputable def guardedFirstRightBlockMonitor
    (source : GuardedRightEntrySource A)
    (code : A.State × A.State) :
    BlockRecordMonitor In₂ In₁
      (PairedRightReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂)) Out₁ := by
  classical
  let U := (pairedRightThreadSystem A code).universalRunDPA
  letI : Fintype U.State := U.stateFinite
  exact {
    State := U.State × PairedRightScanState A × Bool × Bool
    stateFinite := inferInstance
    initial := (U.initial, pairedRightScanInitial A code, true, true)
    step := fun state letter =>
      let rootOK := !state.2.2.1 ||
        decide (source.1.2 letter.1 = letter.2.1.closingFirst)
      let closesFeasible :=
        (pairedEntryRunAutomaton A
          (pairedRightCloseTarget A state.2.1 .first letter)).HasRationalRun ∧
        (pairedEntryRunAutomaton A
          (pairedRightCloseTarget A state.2.1 .both letter)).HasRationalRun
      (U.step state.1 letter,
        pairedRightScanStep A state.2.1 letter, false,
        state.2.2.2 && rootOK && decide closesFeasible)
    priority := fun state =>
      if state.2.2.2 then U.priority state.1 + 2 else 1
  }

section Right

variable
  (source : GuardedRightEntrySource A)
  (code : A.State × A.State) (minimum : A.State)
  (hshape : source.1.1 = Sum.inr (Sum.inl (code, minimum)))

noncomputable abbrev firstRightActivation :=
  guardedRightActivation A source code minimum hshape

theorem guardedFirstRightBlockMonitor_run_eq
    (env : Nat -> In₂ × In₁) : ∀ n,
    (guardedFirstRightBlockMonitor A source code).run
        (pairPlay
          (pairedRightReceiverStrategy (firstRightActivation A source code minimum hshape).lambda)
          (pairedRightSenderStrategy (firstRightActivation A source code minimum hshape).lambda)
          env) n =
      ((pairedRightThreadSystem A code).universalRunDPA.run
          (pairedRightBlockWord
            (firstRightActivation A source code minimum hshape).lambda env) n,
        pairedRightScanAfter A code
          (firstRightActivation A source code minimum hshape).lambda
          (omegaPrefix env n), n == 0, true) := by
  classical
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [BlockRecordMonitor.run, ih]
      simp only [guardedFirstRightBlockMonitor]
      rw [pairedRight_pairPlay_eq_blockWord
        (firstRightActivation A source code minimum hshape).lambda env]
      rw [pairedRightBlockWord_eq_letterAt,
        omegaPrefix_succ, pairedRightScanAfter_append]
      have hfirst := (firstRightActivation A source code minimum hshape).childFeasible
        .first (omegaPrefix env n) (env n)
      have hboth := (firstRightActivation A source code minimum hshape).childFeasible
        .both (omegaPrefix env n) (env n)
      rw [← pairedRightCloseTarget_scanAfter A code
        (firstRightActivation A source code minimum hshape).lambda
        (omegaPrefix env n) (env n) .first] at hfirst
      rw [← pairedRightCloseTarget_scanAfter A code
        (firstRightActivation A source code minimum hshape).lambda
        (omegaPrefix env n) (env n) .both] at hboth
      have hroot :
          (!(n == 0) || decide
            (source.1.2
                (pairedRightBlockLetterAt
                  (firstRightActivation A source code minimum hshape).lambda
                  (omegaPrefix env n) (env n)).1 =
              ((pairedRightBlockLetterAt
                (firstRightActivation A source code minimum hshape).lambda
                (omegaPrefix env n) (env n)).2.1.closingFirst))) = true := by
        cases n with
        | zero =>
            have hm := (firstRightActivation A source code minimum hshape).profile_matches
              (env 0)
            simp [ProcOneEntryOverlapProfile.Matches,
              pairedRightBlockLetterAt] at hm ⊢
            exact hm.symm
        | succ n => rfl
      have hcloses := And.intro hfirst hboth
      rw [hroot, decide_eq_true hcloses]
      simp
      rw [pairedRightBlockWord_eq_letterAt]

/-- The guarded activation lambda realizes the finite first-block monitor. -/
theorem guardedFirstRightBlockMonitor_wins
    (env : Nat -> In₂ × In₁) :
    (guardedFirstRightBlockMonitor A source code).WinsPlay
      (pairPlay
        (pairedRightReceiverStrategy (firstRightActivation A source code minimum hshape).lambda)
        (pairedRightSenderStrategy (firstRightActivation A source code minimum hshape).lambda)
        env) := by
  have huniversal := pairedRightUniversalDPA_accepts_of_forever A code
    (firstRightActivation A source code minimum hshape).lambda
    (firstRightActivation A source code minimum hshape).forever env
  unfold BlockRecordMonitor.WinsPlay
  have hshifted := (natSeqMinEvenParity_add_const (d := 2) ⟨1, rfl⟩).mpr huniversal
  convert hshifted using 1
  funext n
  rw [guardedFirstRightBlockMonitor_run_eq A source code minimum hshape env n]
  rfl

include minimum hshape in
/-- Unconditional finite controller for the guarded first right block. -/
theorem exists_finite_guardedFirstRightController
    [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    [DecidableEq In₁] [DecidableEq In₂] :
    ∃ controller : TransitionRationalTree.{u, max u v x y s, s}
      In₁ (NarrowedBlockLabel In₂ In₁
          (PairedRightReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂)) Out₁
          (guardedFirstRightBlockMonitor.{u, v, x, y, s, 0} A source code).State),
      NarrowedAllThreadsWin
        (guardedFirstRightBlockMonitor.{u, v, x, y, s, 0} A source code)
        controller.labeledTree := by
  refine (block_realizable_iff_implementable_controller_unconditional
    (guardedFirstRightBlockMonitor.{u, v, x, y, s, 0} A source code)).mp ?_
  exact ⟨pairedRightReceiverStrategy
      (firstRightActivation A source code minimum hshape).lambda,
    pairedRightSenderStrategy
      (firstRightActivation A source code minimum hshape).lambda,
    guardedFirstRightBlockMonitor_wins A source code minimum hshape⟩

end Right

/-! ## Process-two / left-block mirror -/

noncomputable def guardedFirstLeftBlockMonitor
    (source : GuardedLeftEntrySource A)
    (code : A.State × A.State) :
    BlockRecordMonitor In₁ In₂
      (PairedLeftReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂)) Out₂ := by
  classical
  let U := (pairedLeftThreadSystem A code).universalRunDPA
  letI : Fintype U.State := U.stateFinite
  exact {
    State := U.State × PairedLeftScanState A × Bool × Bool
    stateFinite := inferInstance
    initial := (U.initial, pairedLeftScanInitial A code, true, true)
    step := fun state letter =>
      let rootOK := !state.2.2.1 ||
        decide (source.1.2 letter.1 = letter.2.1.closingFirst)
      let closesFeasible :=
        (pairedEntryRunAutomaton A
          (pairedLeftCloseTarget A state.2.1 .first letter)).HasRationalRun ∧
        (pairedEntryRunAutomaton A
          (pairedLeftCloseTarget A state.2.1 .both letter)).HasRationalRun
      (U.step state.1 letter,
        pairedLeftScanStep A state.2.1 letter, false,
        state.2.2.2 && rootOK && decide closesFeasible)
    priority := fun state =>
      if state.2.2.2 then U.priority state.1 + 2 else 1
  }

section Left

variable
  (source : GuardedLeftEntrySource A)
  (code : A.State × A.State) (minimum : A.State)
  (hshape : source.1.1 = Sum.inr (Sum.inr (code, minimum)))

noncomputable abbrev firstLeftActivation :=
  guardedLeftActivation A source code minimum hshape

theorem guardedFirstLeftBlockMonitor_run_eq
    (env : Nat -> In₁ × In₂) : ∀ n,
    (guardedFirstLeftBlockMonitor A source code).run
        (pairPlay
          (pairedLeftReceiverStrategy (firstLeftActivation A source code minimum hshape).lambda)
          (pairedLeftSenderStrategy (firstLeftActivation A source code minimum hshape).lambda)
          env) n =
      ((pairedLeftThreadSystem A code).universalRunDPA.run
          (pairedLeftBlockWord
            (firstLeftActivation A source code minimum hshape).lambda env) n,
        pairedLeftScanAfter A code
          (firstLeftActivation A source code minimum hshape).lambda
          (omegaPrefix env n), n == 0, true) := by
  classical
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [BlockRecordMonitor.run, ih]
      simp only [guardedFirstLeftBlockMonitor]
      rw [pairedLeft_pairPlay_eq_blockWord
        (firstLeftActivation A source code minimum hshape).lambda env]
      rw [omegaPrefix_succ, pairedLeftScanAfter_append]
      have hfirst := (firstLeftActivation A source code minimum hshape).childFeasible
        .first (omegaPrefix env n) (env n)
      have hboth := (firstLeftActivation A source code minimum hshape).childFeasible
        .both (omegaPrefix env n) (env n)
      rw [← pairedLeftCloseTarget_scanAfter A code
        (firstLeftActivation A source code minimum hshape).lambda
        (omegaPrefix env n) (env n) .first] at hfirst
      rw [← pairedLeftCloseTarget_scanAfter A code
        (firstLeftActivation A source code minimum hshape).lambda
        (omegaPrefix env n) (env n) .both] at hboth
      have hroot :
          ¬ n = 0 ∨
            source.1.2
                (pairedLeftBlockLetterAt
                  (firstLeftActivation A source code minimum hshape).lambda
                  (omegaPrefix env n) (env n)).1 =
              ((pairedLeftBlockLetterAt
                (firstLeftActivation A source code minimum hshape).lambda
                (omegaPrefix env n) (env n)).2.1.closingFirst) := by
        cases n with
        | zero =>
            right
            have hm := (firstLeftActivation A source code minimum hshape).profile_matches
              (env 0)
            simp [ProcTwoEntryOverlapProfile.Matches, pairedLeftBlockLetterAt] at hm ⊢
            exact hm.symm
        | succ n => exact Or.inl (by omega)
      have hcloses := And.intro hfirst hboth
      simp [pairedLeftBlockWord, hroot, hcloses]

theorem guardedFirstLeftBlockMonitor_wins
    (env : Nat -> In₁ × In₂) :
    (guardedFirstLeftBlockMonitor A source code).WinsPlay
      (pairPlay
        (pairedLeftReceiverStrategy (firstLeftActivation A source code minimum hshape).lambda)
        (pairedLeftSenderStrategy (firstLeftActivation A source code minimum hshape).lambda)
        env) := by
  have huniversal := pairedLeftUniversalDPA_accepts_of_forever A code
    (firstLeftActivation A source code minimum hshape).lambda
    (firstLeftActivation A source code minimum hshape).forever env
  unfold BlockRecordMonitor.WinsPlay
  have hshifted := (natSeqMinEvenParity_add_const (d := 2) ⟨1, rfl⟩).mpr huniversal
  convert hshifted using 1
  funext n
  rw [guardedFirstLeftBlockMonitor_run_eq A source code minimum hshape env n]
  rfl

include minimum hshape in
/-- Unconditional finite controller for the guarded first left block. -/
theorem exists_finite_guardedFirstLeftController
    [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    [DecidableEq In₁] [DecidableEq In₂] :
    ∃ controller : TransitionRationalTree.{v, max u v x y s, s}
      In₂ (NarrowedBlockLabel In₁ In₂
          (PairedLeftReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂)) Out₂
          (guardedFirstLeftBlockMonitor.{u, v, x, y, s, 0} A source code).State),
      NarrowedAllThreadsWin
        (guardedFirstLeftBlockMonitor.{u, v, x, y, s, 0} A source code)
        controller.labeledTree := by
  refine (block_realizable_iff_implementable_controller_unconditional
    (guardedFirstLeftBlockMonitor.{u, v, x, y, s, 0} A source code)).mp ?_
  exact ⟨pairedLeftReceiverStrategy
      (firstLeftActivation A source code minimum hshape).lambda,
    pairedLeftSenderStrategy
      (firstLeftActivation A source code minimum hshape).lambda,
    guardedFirstLeftBlockMonitor_wins A source code minimum hshape⟩

end Left

end DetParityAutomaton

end DistributedSynthesis
