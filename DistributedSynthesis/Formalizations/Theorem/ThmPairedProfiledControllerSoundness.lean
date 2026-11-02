/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledControllerFamily
import DistributedSynthesis.Formalizations.Theorem.ThmPairedEntryControllerSoundness

/-!
# Readback soundness of profiled recurrent controllers

The certificate monitor is sticky: after any failed profile, overlap, or
successor check it emits priority one forever.  Hence every winning play is
safe at every finite prefix.  This module extracts the checked successor and
boundary facts pointwise, ready for the local phase handoff.
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
variable {initialState : PairedProfiledTreeState A}
variable (policy :
  (pairedProfiledEntryRunAutomaton A initialState).RationalTransitionPolicy)

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

/-- Once the right certificate monitor becomes unsafe, it remains unsafe. -/
theorem profiledRightBlockMonitor_safe_false_persists
    (code : A.State × A.State) (minimum : A.State)
    (profile : RightInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (play : Nat → RealizedBlockRound In₂ In₁
      (ProfiledRightReceiverOutput A) Out₁)
    {N : Nat}
    (hfalse : ((profiledRightBlockMonitor.{u, v, x, y, s, 1} A policy code minimum profile).run
      play N).2.2.2.2 = false) :
    ∀ n, N ≤ n →
      ((profiledRightBlockMonitor.{u, v, x, y, s, 1} A policy code minimum profile).run
        play n).2.2.2.2 = false := by
  classical
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero => simpa using hfalse
  | succ k ih =>
      rw [Nat.add_succ, BlockRecordMonitor.run]
      simp only [profiledRightBlockMonitor]
      change
        (((profiledRightBlockMonitor.{u, v, x, y, s, 1} A policy code minimum profile).run
          play (N + k)).2.2.2.2 && _ && decide _ && decide _) = false
      rw [ih (Nat.le_add_right N k)]
      rfl

/-- A winning right certificate play is safe at every prefix. -/
theorem profiledRightBlockMonitor_safe_of_wins
    (code : A.State × A.State) (minimum : A.State)
    (profile : RightInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (play : Nat → RealizedBlockRound In₂ In₁
      (ProfiledRightReceiverOutput A) Out₁)
    (hwin : (profiledRightBlockMonitor.{u, v, x, y, s, 1} A policy code minimum profile).WinsPlay
      play) (n : Nat) :
    ((profiledRightBlockMonitor.{u, v, x, y, s, 1} A policy code minimum profile).run
      play n).2.2.2.2 = true := by
  by_contra hnot
  have hfalse :
      ((profiledRightBlockMonitor.{u, v, x, y, s, 1} A policy code minimum profile).run
        play n).2.2.2.2 = false := Bool.eq_false_of_not_eq_true hnot
  have hpersist := profiledRightBlockMonitor_safe_false_persists
    A policy code minimum profile play hfalse
  have heventual : ∀ k, n ≤ k →
      (profiledRightBlockMonitor.{u, v, x, y, s, 1} A policy code minimum profile).priority
        ((profiledRightBlockMonitor.{u, v, x, y, s, 1} A policy code minimum profile).run
          play k) = 1 := by
    intro k hk
    have hs := hpersist k hk
    change
      (if ((profiledRightBlockMonitor.{u, v, x, y, s, 1} A policy code minimum profile).run
        play k).2.2.2.2 then _ else 1) = 1
    rw [hs]
    rfl
  exact not_natSeqMinEvenParity_of_eventually_one _ n heventual hwin

/-- The first informed action of every winning narrowed right block realizes
the initial action profile stored in its profiled source. -/
theorem profiledRight_rootProfile_of_wins
    (code : A.State × A.State) (minimum : A.State)
    (profile : RightInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (play : Nat → RealizedBlockRound In₂ In₁
      (ProfiledRightReceiverOutput A) Out₁)
    (hwin : (profiledRightBlockMonitor.{u, v, x, y, s, 1}
      A policy code minimum profile).WinsPlay play) :
    pairedRightInformedForRow .first (play 0).2.1.physical =
      profile (play 0).1 := by
  classical
  have hsafe := profiledRightBlockMonitor_safe_of_wins A policy code minimum
    profile play hwin 1
  rw [BlockRecordMonitor.run] at hsafe
  simp only [BlockRecordMonitor.run, profiledRightBlockMonitor, Bool.and_eq_true,
    Bool.not_true, Bool.false_or, decide_eq_true_eq] at hsafe
  exact hsafe.1.1.2

/-- Every successor certificate emitted on a winning right play has the
checked erased DPA target and is an allowed profiled policy edge. -/
theorem profiledRight_targetsSafe_of_wins
    (code : A.State × A.State) (minimum : A.State)
    (profile : RightInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (play : Nat → RealizedBlockRound In₂ In₁
      (ProfiledRightReceiverOutput A) Out₁)
    (hwin : (profiledRightBlockMonitor.{u, v, x, y, s, 1} A policy code minimum profile).WinsPlay
      play) (n : Nat) :
    ∀ row,
      erasePairedProfiledState A ((play n).2.1.target row) =
          pairedRightCloseTarget A
            (((profiledRightBlockMonitor.{u, v, x, y, s, 1} A policy code minimum profile).run
              play n).2.1) row (profiledRightPhysicalLetter A (play n)) ∧
        PairedProfiledRationalPolicy.Allowed A policy
          (.inr (.inl ((code, minimum), profile)))
          ((play n).2.1.target row) := by
  classical
  have hsafeNext := profiledRightBlockMonitor_safe_of_wins
    A policy code minimum profile play hwin (n + 1)
  rw [BlockRecordMonitor.run] at hsafeNext
  simp only [profiledRightBlockMonitor, Bool.and_eq_true,
    decide_eq_true_eq] at hsafeNext
  exact hsafeNext.2

/-- The delayed closing-profile equality checked between two consecutive
right-block rounds. -/
theorem profiledRight_overlap_of_wins
    (code : A.State × A.State) (minimum : A.State)
    (profile : RightInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (play : Nat → RealizedBlockRound In₂ In₁
      (ProfiledRightReceiverOutput A) Out₁)
    (hwin : (profiledRightBlockMonitor.{u, v, x, y, s, 1}
      A policy code minimum profile).WinsPlay play)
    (n : Nat) (row : PairedEntryRow)
    (expected : LeftInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (hpending :
      ((profiledRightBlockMonitor.{u, v, x, y, s, 1}
        A policy code minimum profile).run play n).2.2.1 row =
          some expected) :
    pairedRightClosingForRow row (play n).2.1.physical =
      expected ((play n).1.2, (play n).1.1) := by
  classical
  have hsafeNext := profiledRightBlockMonitor_safe_of_wins
    A policy code minimum profile play hwin (n + 1)
  rw [BlockRecordMonitor.run] at hsafeNext
  simp only [profiledRightBlockMonitor, Bool.and_eq_true,
    decide_eq_true_eq] at hsafeNext
  exact hsafeNext.1.2 row expected hpending

end

/-! ## Left mirror -/

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

theorem profiledLeftBlockMonitor_safe_false_persists
    (code : A.State × A.State) (minimum : A.State)
    (profile : LeftInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (play : Nat → RealizedBlockRound In₁ In₂
      (ProfiledLeftReceiverOutput A) Out₂)
    {N : Nat}
    (hfalse : ((profiledLeftBlockMonitor.{u, v, x, y, s, 1} A policy code minimum profile).run
      play N).2.2.2.2 = false) :
    ∀ n, N ≤ n →
      ((profiledLeftBlockMonitor.{u, v, x, y, s, 1} A policy code minimum profile).run
        play n).2.2.2.2 = false := by
  classical
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero => simpa using hfalse
  | succ k ih =>
      rw [Nat.add_succ, BlockRecordMonitor.run]
      simp only [profiledLeftBlockMonitor]
      change
        (((profiledLeftBlockMonitor.{u, v, x, y, s, 1} A policy code minimum profile).run
          play (N + k)).2.2.2.2 && _ && decide _ && decide _) = false
      rw [ih (Nat.le_add_right N k)]
      rfl

theorem profiledLeftBlockMonitor_safe_of_wins
    (code : A.State × A.State) (minimum : A.State)
    (profile : LeftInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (play : Nat → RealizedBlockRound In₁ In₂
      (ProfiledLeftReceiverOutput A) Out₂)
    (hwin : (profiledLeftBlockMonitor.{u, v, x, y, s, 1} A policy code minimum profile).WinsPlay
      play) (n : Nat) :
    ((profiledLeftBlockMonitor.{u, v, x, y, s, 1} A policy code minimum profile).run
      play n).2.2.2.2 = true := by
  by_contra hnot
  have hfalse :
      ((profiledLeftBlockMonitor.{u, v, x, y, s, 1} A policy code minimum profile).run
        play n).2.2.2.2 = false := Bool.eq_false_of_not_eq_true hnot
  have hpersist := profiledLeftBlockMonitor_safe_false_persists
    A policy code minimum profile play hfalse
  have heventual : ∀ k, n ≤ k →
      (profiledLeftBlockMonitor.{u, v, x, y, s, 1} A policy code minimum profile).priority
        ((profiledLeftBlockMonitor.{u, v, x, y, s, 1} A policy code minimum profile).run
          play k) = 1 := by
    intro k hk
    have hs := hpersist k hk
    change
      (if ((profiledLeftBlockMonitor.{u, v, x, y, s, 1} A policy code minimum profile).run
        play k).2.2.2.2 then _ else 1) = 1
    rw [hs]
    rfl
  exact not_natSeqMinEvenParity_of_eventually_one _ n heventual hwin

/-- Left mirror of `profiledRight_rootProfile_of_wins`. -/
theorem profiledLeft_rootProfile_of_wins
    (code : A.State × A.State) (minimum : A.State)
    (profile : LeftInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (play : Nat → RealizedBlockRound In₁ In₂
      (ProfiledLeftReceiverOutput A) Out₂)
    (hwin : (profiledLeftBlockMonitor.{u, v, x, y, s, 1}
      A policy code minimum profile).WinsPlay play) :
    pairedLeftInformedForRow .first (play 0).2.1.physical =
      profile (play 0).1 := by
  classical
  have hsafe := profiledLeftBlockMonitor_safe_of_wins A policy code minimum
    profile play hwin 1
  rw [BlockRecordMonitor.run] at hsafe
  simp only [BlockRecordMonitor.run, profiledLeftBlockMonitor, Bool.and_eq_true,
    Bool.not_true, Bool.false_or, decide_eq_true_eq] at hsafe
  exact hsafe.1.1.2

theorem profiledLeft_targetsSafe_of_wins
    (code : A.State × A.State) (minimum : A.State)
    (profile : LeftInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (play : Nat → RealizedBlockRound In₁ In₂
      (ProfiledLeftReceiverOutput A) Out₂)
    (hwin : (profiledLeftBlockMonitor.{u, v, x, y, s, 1} A policy code minimum profile).WinsPlay
      play) (n : Nat) :
    ∀ row,
      erasePairedProfiledState A ((play n).2.1.target row) =
          pairedLeftCloseTarget A
            (((profiledLeftBlockMonitor.{u, v, x, y, s, 1} A policy code minimum profile).run
              play n).2.1) row (profiledLeftPhysicalLetter A (play n)) ∧
        PairedProfiledRationalPolicy.Allowed A policy
          (.inr (.inr ((code, minimum), profile)))
          ((play n).2.1.target row) := by
  classical
  have hsafeNext := profiledLeftBlockMonitor_safe_of_wins
    A policy code minimum profile play hwin (n + 1)
  rw [BlockRecordMonitor.run] at hsafeNext
  simp only [profiledLeftBlockMonitor, Bool.and_eq_true,
    decide_eq_true_eq] at hsafeNext
  exact hsafeNext.2

/-- Left mirror of `profiledRight_overlap_of_wins`. -/
theorem profiledLeft_overlap_of_wins
    (code : A.State × A.State) (minimum : A.State)
    (profile : LeftInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (play : Nat → RealizedBlockRound In₁ In₂
      (ProfiledLeftReceiverOutput A) Out₂)
    (hwin : (profiledLeftBlockMonitor.{u, v, x, y, s, 1}
      A policy code minimum profile).WinsPlay play)
    (n : Nat) (row : PairedEntryRow)
    (expected : RightInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (hpending :
      ((profiledLeftBlockMonitor.{u, v, x, y, s, 1}
        A policy code minimum profile).run play n).2.2.1 row =
          some expected) :
    pairedLeftClosingForRow row (play n).2.1.physical =
      expected ((play n).1.2, (play n).1.1) := by
  classical
  have hsafeNext := profiledLeftBlockMonitor_safe_of_wins
    A policy code minimum profile play hwin (n + 1)
  rw [BlockRecordMonitor.run] at hsafeNext
  simp only [profiledLeftBlockMonitor, Bool.and_eq_true,
    decide_eq_true_eq] at hsafeNext
  exact hsafeNext.1.2 row expected hpending

end

end

end


end DetParityAutomaton

end DistributedSynthesis
