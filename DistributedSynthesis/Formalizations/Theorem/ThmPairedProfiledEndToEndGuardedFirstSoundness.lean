/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndGuardedFirstHandoff

/-!
# Soundness of the one-policy guarded-first controllers

Winning the strengthened sticky monitor forces every emitted child to be an
actual root successor of the supplied guarded policy.  Thus sender narrowing
cannot escape from the one common policy selected before streaming begins.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

/-! ## First-right orientation -/

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

theorem endToEndGuardedFirstRight_safe_false_persists
    (target : PairedProfiledTreeState A)
    (overlap : ProcOneEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (policy : (rightProfiledGuardedAutomaton A target overlap).RationalTransitionPolicy)
    (code : A.State × A.State) (minimum : A.State)
    (profile : RightInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (play : Nat → RealizedBlockRound In₂ In₁
      (ProfiledRightReceiverOutput A) Out₁)
    {N : Nat}
    (hfalse : ((endToEndGuardedFirstRightBlockMonitor.{u, v, x, y, s, 1}
      A target overlap policy code minimum profile).run play N).2.2.2.2 = false) :
    ∀ n, N ≤ n →
      ((endToEndGuardedFirstRightBlockMonitor.{u, v, x, y, s, 1}
        A target overlap policy code minimum profile).run play n).2.2.2.2 = false := by
  classical
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero => simpa using hfalse
  | succ k ih =>
      rw [Nat.add_succ, BlockRecordMonitor.run]
      simp only [endToEndGuardedFirstRightBlockMonitor]
      change
        (((((endToEndGuardedFirstRightBlockMonitor.{u, v, x, y, s, 1}
          A target overlap policy code minimum profile).run play (N + k)).2.2.2.2 && _) &&
          _) && decide _ && decide _) = false
      rw [ih (Nat.le_add_right N k)]
      rfl

theorem endToEndGuardedFirstRight_safe_of_wins
    (target : PairedProfiledTreeState A)
    (overlap : ProcOneEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (policy : (rightProfiledGuardedAutomaton A target overlap).RationalTransitionPolicy)
    (code : A.State × A.State) (minimum : A.State)
    (profile : RightInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (play : Nat → RealizedBlockRound In₂ In₁
      (ProfiledRightReceiverOutput A) Out₁)
    (hwin : (endToEndGuardedFirstRightBlockMonitor.{u, v, x, y, s, 1}
      A target overlap policy code minimum profile).WinsPlay play) (n : Nat) :
    ((endToEndGuardedFirstRightBlockMonitor.{u, v, x, y, s, 1}
      A target overlap policy code minimum profile).run play n).2.2.2.2 = true := by
  by_contra hnot
  have hfalse := Bool.eq_false_of_not_eq_true hnot
  have hpersist := endToEndGuardedFirstRight_safe_false_persists
    A target overlap policy code minimum profile play hfalse
  have heventual : ∀ k, n ≤ k →
      (endToEndGuardedFirstRightBlockMonitor.{u, v, x, y, s, 1}
        A target overlap policy code minimum profile).priority
        ((endToEndGuardedFirstRightBlockMonitor.{u, v, x, y, s, 1}
          A target overlap policy code minimum profile).run play k) = 1 := by
    intro k hk
    have hs := hpersist k hk
    change (if ((endToEndGuardedFirstRightBlockMonitor.{u, v, x, y, s, 1}
      A target overlap policy code minimum profile).run play k).2.2.2.2
      then _ else 1) = 1
    rw [hs]
    rfl
  exact not_natSeqMinEvenParity_of_eventually_one _ n heventual hwin

/-- Pointwise common-policy edge and erased-target soundness. -/
theorem endToEndGuardedFirstRight_targetsSafe_of_wins
    (target : PairedProfiledTreeState A)
    (overlap : ProcOneEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (policy : (rightProfiledGuardedAutomaton A target overlap).RationalTransitionPolicy)
    (code : A.State × A.State) (minimum : A.State)
    (profile : RightInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (play : Nat → RealizedBlockRound In₂ In₁
      (ProfiledRightReceiverOutput A) Out₁)
    (hwin : (endToEndGuardedFirstRightBlockMonitor.{u, v, x, y, s, 1}
      A target overlap policy code minimum profile).WinsPlay play) (n : Nat) :
    ∀ row,
      erasePairedProfiledState A ((play n).2.1.target row) =
          pairedRightCloseTarget A
            (((endToEndGuardedFirstRightBlockMonitor.{u, v, x, y, s, 1}
              A target overlap policy code minimum profile).run play n).2.1) row
            (profiledRightPhysicalLetter A (play n)) ∧
        ProfiledGuardedRightPolicyAllows A target overlap policy
          ((play n).2.1.target row) := by
  classical
  have hsafeNext := endToEndGuardedFirstRight_safe_of_wins A target overlap
    policy code minimum profile play hwin (n + 1)
  rw [BlockRecordMonitor.run] at hsafeNext
  simp only [endToEndGuardedFirstRightBlockMonitor, Bool.and_eq_true,
    decide_eq_true_eq] at hsafeNext
  exact hsafeNext.2

/-- The delayed closing-profile equality checked between consecutive rounds
of a winning guarded first-right block. -/
theorem endToEndGuardedFirstRight_overlap_of_wins
    (target : PairedProfiledTreeState A)
    (overlap : ProcOneEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (policy : (rightProfiledGuardedAutomaton A target overlap).RationalTransitionPolicy)
    (code : A.State × A.State) (minimum : A.State)
    (profile : RightInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (play : Nat → RealizedBlockRound In₂ In₁
      (ProfiledRightReceiverOutput A) Out₁)
    (hwin : (endToEndGuardedFirstRightBlockMonitor.{u, v, x, y, s, 1}
      A target overlap policy code minimum profile).WinsPlay play)
    (n : Nat) (row : PairedEntryRow)
    (expected : LeftInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (hpending :
      ((endToEndGuardedFirstRightBlockMonitor.{u, v, x, y, s, 1}
        A target overlap policy code minimum profile).run play n).2.2.1 row =
          some expected) :
    pairedRightClosingForRow row (play n).2.1.physical =
      expected ((play n).1.2, (play n).1.1) := by
  classical
  have hsafeNext := endToEndGuardedFirstRight_safe_of_wins A target overlap
    policy code minimum profile play hwin (n + 1)
  rw [BlockRecordMonitor.run] at hsafeNext
  simp only [endToEndGuardedFirstRightBlockMonitor, Bool.and_eq_true,
    decide_eq_true_eq] at hsafeNext
  exact hsafeNext.1.2 row expected hpending

/-- In particular the exact emitted target has a rational run inherited from
the supplied guarded policy. -/
theorem endToEndGuardedFirstRight_target_hasRationalRun_of_wins
    (target : PairedProfiledTreeState A)
    (overlap : ProcOneEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (policy : (rightProfiledGuardedAutomaton A target overlap).RationalTransitionPolicy)
    (code : A.State × A.State) (minimum : A.State)
    (profile : RightInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (play : Nat → RealizedBlockRound In₂ In₁
      (ProfiledRightReceiverOutput A) Out₁)
    (hwin : (endToEndGuardedFirstRightBlockMonitor.{u, v, x, y, s, 1}
      A target overlap policy code minimum profile).WinsPlay play)
    (n : Nat) (row : PairedEntryRow) :
    (pairedProfiledEntryRunAutomaton A ((play n).2.1.target row)).HasRationalRun :=
  hasRationalRun_of_profiledGuardedRightPolicyAllows A target overlap policy
    ((play n).2.1.target row)
    (endToEndGuardedFirstRight_targetsSafe_of_wins A target overlap policy
      code minimum profile play hwin n row).2

end

/-! ## First-left mirror -/

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

theorem endToEndGuardedFirstLeft_safe_false_persists
    (target : PairedProfiledTreeState A)
    (overlap : ProcTwoEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (policy : (leftProfiledGuardedAutomaton A target overlap).RationalTransitionPolicy)
    (code : A.State × A.State) (minimum : A.State)
    (profile : LeftInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (play : Nat → RealizedBlockRound In₁ In₂
      (ProfiledLeftReceiverOutput A) Out₂)
    {N : Nat}
    (hfalse : ((endToEndGuardedFirstLeftBlockMonitor.{u, v, x, y, s, 1}
      A target overlap policy code minimum profile).run play N).2.2.2.2 = false) :
    ∀ n, N ≤ n →
      ((endToEndGuardedFirstLeftBlockMonitor.{u, v, x, y, s, 1}
        A target overlap policy code minimum profile).run play n).2.2.2.2 = false := by
  classical
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero => simpa using hfalse
  | succ k ih =>
      rw [Nat.add_succ, BlockRecordMonitor.run]
      simp only [endToEndGuardedFirstLeftBlockMonitor]
      change
        (((((endToEndGuardedFirstLeftBlockMonitor.{u, v, x, y, s, 1}
          A target overlap policy code minimum profile).run play (N + k)).2.2.2.2 && _) &&
          _) && decide _ && decide _) = false
      rw [ih (Nat.le_add_right N k)]
      rfl

theorem endToEndGuardedFirstLeft_safe_of_wins
    (target : PairedProfiledTreeState A)
    (overlap : ProcTwoEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (policy : (leftProfiledGuardedAutomaton A target overlap).RationalTransitionPolicy)
    (code : A.State × A.State) (minimum : A.State)
    (profile : LeftInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (play : Nat → RealizedBlockRound In₁ In₂
      (ProfiledLeftReceiverOutput A) Out₂)
    (hwin : (endToEndGuardedFirstLeftBlockMonitor.{u, v, x, y, s, 1}
      A target overlap policy code minimum profile).WinsPlay play) (n : Nat) :
    ((endToEndGuardedFirstLeftBlockMonitor.{u, v, x, y, s, 1}
      A target overlap policy code minimum profile).run play n).2.2.2.2 = true := by
  by_contra hnot
  have hfalse := Bool.eq_false_of_not_eq_true hnot
  have hpersist := endToEndGuardedFirstLeft_safe_false_persists
    A target overlap policy code minimum profile play hfalse
  have heventual : ∀ k, n ≤ k →
      (endToEndGuardedFirstLeftBlockMonitor.{u, v, x, y, s, 1}
        A target overlap policy code minimum profile).priority
        ((endToEndGuardedFirstLeftBlockMonitor.{u, v, x, y, s, 1}
          A target overlap policy code minimum profile).run play k) = 1 := by
    intro k hk
    have hs := hpersist k hk
    change (if ((endToEndGuardedFirstLeftBlockMonitor.{u, v, x, y, s, 1}
      A target overlap policy code minimum profile).run play k).2.2.2.2
      then _ else 1) = 1
    rw [hs]
    rfl
  exact not_natSeqMinEvenParity_of_eventually_one _ n heventual hwin

theorem endToEndGuardedFirstLeft_targetsSafe_of_wins
    (target : PairedProfiledTreeState A)
    (overlap : ProcTwoEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (policy : (leftProfiledGuardedAutomaton A target overlap).RationalTransitionPolicy)
    (code : A.State × A.State) (minimum : A.State)
    (profile : LeftInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (play : Nat → RealizedBlockRound In₁ In₂
      (ProfiledLeftReceiverOutput A) Out₂)
    (hwin : (endToEndGuardedFirstLeftBlockMonitor.{u, v, x, y, s, 1}
      A target overlap policy code minimum profile).WinsPlay play) (n : Nat) :
    ∀ row,
      erasePairedProfiledState A ((play n).2.1.target row) =
          pairedLeftCloseTarget A
            (((endToEndGuardedFirstLeftBlockMonitor.{u, v, x, y, s, 1}
              A target overlap policy code minimum profile).run play n).2.1) row
            (profiledLeftPhysicalLetter A (play n)) ∧
        ProfiledGuardedLeftPolicyAllows A target overlap policy
          ((play n).2.1.target row) := by
  classical
  have hsafeNext := endToEndGuardedFirstLeft_safe_of_wins A target overlap
    policy code minimum profile play hwin (n + 1)
  rw [BlockRecordMonitor.run] at hsafeNext
  simp only [endToEndGuardedFirstLeftBlockMonitor, Bool.and_eq_true,
    decide_eq_true_eq] at hsafeNext
  exact hsafeNext.2

/-- Left mirror of `endToEndGuardedFirstRight_overlap_of_wins`. -/
theorem endToEndGuardedFirstLeft_overlap_of_wins
    (target : PairedProfiledTreeState A)
    (overlap : ProcTwoEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (policy : (leftProfiledGuardedAutomaton A target overlap).RationalTransitionPolicy)
    (code : A.State × A.State) (minimum : A.State)
    (profile : LeftInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (play : Nat → RealizedBlockRound In₁ In₂
      (ProfiledLeftReceiverOutput A) Out₂)
    (hwin : (endToEndGuardedFirstLeftBlockMonitor.{u, v, x, y, s, 1}
      A target overlap policy code minimum profile).WinsPlay play)
    (n : Nat) (row : PairedEntryRow)
    (expected : RightInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (hpending :
      ((endToEndGuardedFirstLeftBlockMonitor.{u, v, x, y, s, 1}
        A target overlap policy code minimum profile).run play n).2.2.1 row =
          some expected) :
    pairedLeftClosingForRow row (play n).2.1.physical =
      expected ((play n).1.2, (play n).1.1) := by
  classical
  have hsafeNext := endToEndGuardedFirstLeft_safe_of_wins A target overlap
    policy code minimum profile play hwin (n + 1)
  rw [BlockRecordMonitor.run] at hsafeNext
  simp only [endToEndGuardedFirstLeftBlockMonitor, Bool.and_eq_true,
    decide_eq_true_eq] at hsafeNext
  exact hsafeNext.1.2 row expected hpending

theorem endToEndGuardedFirstLeft_target_hasRationalRun_of_wins
    (target : PairedProfiledTreeState A)
    (overlap : ProcTwoEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (policy : (leftProfiledGuardedAutomaton A target overlap).RationalTransitionPolicy)
    (code : A.State × A.State) (minimum : A.State)
    (profile : LeftInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (play : Nat → RealizedBlockRound In₁ In₂
      (ProfiledLeftReceiverOutput A) Out₂)
    (hwin : (endToEndGuardedFirstLeftBlockMonitor.{u, v, x, y, s, 1}
      A target overlap policy code minimum profile).WinsPlay play)
    (n : Nat) (row : PairedEntryRow) :
    (pairedProfiledEntryRunAutomaton A ((play n).2.1.target row)).HasRationalRun :=
  hasRationalRun_of_profiledGuardedLeftPolicyAllows A target overlap policy
    ((play n).2.1.target row)
    (endToEndGuardedFirstLeft_targetsSafe_of_wins A target overlap policy
      code minimum profile play hwin n row).2

end

end


end DetParityAutomaton

end DistributedSynthesis
