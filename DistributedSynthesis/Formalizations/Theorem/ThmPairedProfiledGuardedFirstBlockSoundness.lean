/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledGuardedFirstBlockRegularization

/-!
# Soundness of profiled guarded first-block controllers

Winning the sticky first-block monitor recovers every checked finite handoff
fact.  In particular, each emitted child is immediately a
`FeasibleProfiledPairedState`, its erasure is the monitor's DPA close target,
and its stored profile agrees with the next physical boundary action.
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

/-! ## Right orientation -/

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

theorem profiledGuardedFirstRight_safe_false_persists
    (source : ProfiledGuardedRightEntrySource A)
    (code : A.State × A.State) (minimum : A.State)
    (initialProfile : RightInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (play : Nat → RealizedBlockRound In₂ In₁
      (ProfiledRightReceiverOutput A) Out₁)
    {N : Nat}
    (hfalse : ((profiledGuardedFirstRightBlockMonitor.{u, v, x, y, s, 1}
      A source code minimum initialProfile).run play N).2.2.2.2 = false) :
    ∀ n, N ≤ n →
      ((profiledGuardedFirstRightBlockMonitor.{u, v, x, y, s, 1}
        A source code minimum initialProfile).run play n).2.2.2.2 = false := by
  classical
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero => simpa using hfalse
  | succ k ih =>
      rw [Nat.add_succ, BlockRecordMonitor.run]
      simp only [profiledGuardedFirstRightBlockMonitor]
      change
        (((((profiledGuardedFirstRightBlockMonitor.{u, v, x, y, s, 1}
          A source code minimum initialProfile).run play (N + k)).2.2.2.2 && _) &&
          _) && decide _ && decide _) = false
      rw [ih (Nat.le_add_right N k)]
      rfl

theorem profiledGuardedFirstRight_safe_of_wins
    (source : ProfiledGuardedRightEntrySource A)
    (code : A.State × A.State) (minimum : A.State)
    (initialProfile : RightInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (play : Nat → RealizedBlockRound In₂ In₁
      (ProfiledRightReceiverOutput A) Out₁)
    (hwin : (profiledGuardedFirstRightBlockMonitor.{u, v, x, y, s, 1}
      A source code minimum initialProfile).WinsPlay play) (n : Nat) :
    ((profiledGuardedFirstRightBlockMonitor.{u, v, x, y, s, 1}
      A source code minimum initialProfile).run play n).2.2.2.2 = true := by
  by_contra hnot
  have hfalse := Bool.eq_false_of_not_eq_true hnot
  have hpersist := profiledGuardedFirstRight_safe_false_persists
    A source code minimum initialProfile play hfalse
  have heventual : ∀ k, n ≤ k →
      (profiledGuardedFirstRightBlockMonitor.{u, v, x, y, s, 1}
        A source code minimum initialProfile).priority
        ((profiledGuardedFirstRightBlockMonitor.{u, v, x, y, s, 1}
          A source code minimum initialProfile).run play k) = 1 := by
    intro k hk
    have hs := hpersist k hk
    change (if ((profiledGuardedFirstRightBlockMonitor.{u, v, x, y, s, 1}
      A source code minimum initialProfile).run play k).2.2.2.2
      then _ else 1) = 1
    rw [hs]
    rfl
  exact not_natSeqMinEvenParity_of_eventually_one _ n heventual hwin

/-- Every emitted right child has the correct erasure and a rational run. -/
theorem profiledGuardedFirstRight_targetsSafe_of_wins
    (source : ProfiledGuardedRightEntrySource A)
    (code : A.State × A.State) (minimum : A.State)
    (initialProfile : RightInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (play : Nat → RealizedBlockRound In₂ In₁
      (ProfiledRightReceiverOutput A) Out₁)
    (hwin : (profiledGuardedFirstRightBlockMonitor.{u, v, x, y, s, 1}
      A source code minimum initialProfile).WinsPlay play) (n : Nat) :
    ∀ row,
      erasePairedProfiledState A ((play n).2.1.target row) =
          pairedRightCloseTarget A
            (((profiledGuardedFirstRightBlockMonitor.{u, v, x, y, s, 1}
              A source code minimum initialProfile).run play n).2.1) row
            (profiledRightPhysicalLetter A (play n)) ∧
        (pairedProfiledEntryRunAutomaton A
          ((play n).2.1.target row)).HasRationalRun := by
  classical
  have hsafeNext := profiledGuardedFirstRight_safe_of_wins A source code
    minimum initialProfile play hwin (n + 1)
  rw [BlockRecordMonitor.run] at hsafeNext
  simp only [profiledGuardedFirstRightBlockMonitor, Bool.and_eq_true,
    decide_eq_true_eq] at hsafeNext
  exact hsafeNext.2

end

/-- Package an emitted right child as the exact next profiled bank key. -/
noncomputable def profiledGuardedFirstRight_childFeasible_of_wins
    (source : ProfiledGuardedRightEntrySource A)
    (code : A.State × A.State) (minimum : A.State)
    (initialProfile : RightInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (play : Nat → RealizedBlockRound In₂ In₁
      (ProfiledRightReceiverOutput A) Out₁)
    (hwin : (profiledGuardedFirstRightBlockMonitor.{u, v, x, y, s, 1}
      A source code minimum initialProfile).WinsPlay play)
    (n : Nat) (row : PairedEntryRow) : FeasibleProfiledPairedState A :=
  ⟨(play n).2.1.target row,
    (profiledGuardedFirstRight_targetsSafe_of_wins A source code minimum
      initialProfile play hwin n row).2⟩

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Delayed boundary equality on a winning exceptional right block. -/
theorem profiledGuardedFirstRight_overlap_of_wins
    (source : ProfiledGuardedRightEntrySource A)
    (code : A.State × A.State) (minimum : A.State)
    (initialProfile : RightInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (play : Nat → RealizedBlockRound In₂ In₁
      (ProfiledRightReceiverOutput A) Out₁)
    (hwin : (profiledGuardedFirstRightBlockMonitor.{u, v, x, y, s, 1}
      A source code minimum initialProfile).WinsPlay play)
    (n : Nat) (row : PairedEntryRow)
    (expected : LeftInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (hpending :
      ((profiledGuardedFirstRightBlockMonitor.{u, v, x, y, s, 1}
        A source code minimum initialProfile).run play n).2.2.1 row =
          some expected) :
    pairedRightClosingForRow row (play n).2.1.physical =
      expected ((play n).1.2, (play n).1.1) := by
  classical
  have hsafeNext := profiledGuardedFirstRight_safe_of_wins A source code
    minimum initialProfile play hwin (n + 1)
  rw [BlockRecordMonitor.run] at hsafeNext
  simp only [profiledGuardedFirstRightBlockMonitor, Bool.and_eq_true,
    decide_eq_true_eq] at hsafeNext
  exact hsafeNext.1.2 row expected hpending

/-! ## Left orientation -/

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

theorem profiledGuardedFirstLeft_safe_false_persists
    (source : ProfiledGuardedLeftEntrySource A)
    (code : A.State × A.State) (minimum : A.State)
    (initialProfile : LeftInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (play : Nat → RealizedBlockRound In₁ In₂
      (ProfiledLeftReceiverOutput A) Out₂)
    {N : Nat}
    (hfalse : ((profiledGuardedFirstLeftBlockMonitor.{u, v, x, y, s, 1}
      A source code minimum initialProfile).run play N).2.2.2.2 = false) :
    ∀ n, N ≤ n →
      ((profiledGuardedFirstLeftBlockMonitor.{u, v, x, y, s, 1}
        A source code minimum initialProfile).run play n).2.2.2.2 = false := by
  classical
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero => simpa using hfalse
  | succ k ih =>
      rw [Nat.add_succ, BlockRecordMonitor.run]
      simp only [profiledGuardedFirstLeftBlockMonitor]
      change
        (((((profiledGuardedFirstLeftBlockMonitor.{u, v, x, y, s, 1}
          A source code minimum initialProfile).run play (N + k)).2.2.2.2 && _) &&
          _) && decide _ && decide _) = false
      rw [ih (Nat.le_add_right N k)]
      rfl

theorem profiledGuardedFirstLeft_safe_of_wins
    (source : ProfiledGuardedLeftEntrySource A)
    (code : A.State × A.State) (minimum : A.State)
    (initialProfile : LeftInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (play : Nat → RealizedBlockRound In₁ In₂
      (ProfiledLeftReceiverOutput A) Out₂)
    (hwin : (profiledGuardedFirstLeftBlockMonitor.{u, v, x, y, s, 1}
      A source code minimum initialProfile).WinsPlay play) (n : Nat) :
    ((profiledGuardedFirstLeftBlockMonitor.{u, v, x, y, s, 1}
      A source code minimum initialProfile).run play n).2.2.2.2 = true := by
  by_contra hnot
  have hfalse := Bool.eq_false_of_not_eq_true hnot
  have hpersist := profiledGuardedFirstLeft_safe_false_persists
    A source code minimum initialProfile play hfalse
  have heventual : ∀ k, n ≤ k →
      (profiledGuardedFirstLeftBlockMonitor.{u, v, x, y, s, 1}
        A source code minimum initialProfile).priority
        ((profiledGuardedFirstLeftBlockMonitor.{u, v, x, y, s, 1}
          A source code minimum initialProfile).run play k) = 1 := by
    intro k hk
    have hs := hpersist k hk
    change (if ((profiledGuardedFirstLeftBlockMonitor.{u, v, x, y, s, 1}
      A source code minimum initialProfile).run play k).2.2.2.2
      then _ else 1) = 1
    rw [hs]
    rfl
  exact not_natSeqMinEvenParity_of_eventually_one _ n heventual hwin

theorem profiledGuardedFirstLeft_targetsSafe_of_wins
    (source : ProfiledGuardedLeftEntrySource A)
    (code : A.State × A.State) (minimum : A.State)
    (initialProfile : LeftInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (play : Nat → RealizedBlockRound In₁ In₂
      (ProfiledLeftReceiverOutput A) Out₂)
    (hwin : (profiledGuardedFirstLeftBlockMonitor.{u, v, x, y, s, 1}
      A source code minimum initialProfile).WinsPlay play) (n : Nat) :
    ∀ row,
      erasePairedProfiledState A ((play n).2.1.target row) =
          pairedLeftCloseTarget A
            (((profiledGuardedFirstLeftBlockMonitor.{u, v, x, y, s, 1}
              A source code minimum initialProfile).run play n).2.1) row
            (profiledLeftPhysicalLetter A (play n)) ∧
        (pairedProfiledEntryRunAutomaton A
          ((play n).2.1.target row)).HasRationalRun := by
  classical
  have hsafeNext := profiledGuardedFirstLeft_safe_of_wins A source code
    minimum initialProfile play hwin (n + 1)
  rw [BlockRecordMonitor.run] at hsafeNext
  simp only [profiledGuardedFirstLeftBlockMonitor, Bool.and_eq_true,
    decide_eq_true_eq] at hsafeNext
  exact hsafeNext.2

end

noncomputable def profiledGuardedFirstLeft_childFeasible_of_wins
    (source : ProfiledGuardedLeftEntrySource A)
    (code : A.State × A.State) (minimum : A.State)
    (initialProfile : LeftInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (play : Nat → RealizedBlockRound In₁ In₂
      (ProfiledLeftReceiverOutput A) Out₂)
    (hwin : (profiledGuardedFirstLeftBlockMonitor.{u, v, x, y, s, 1}
      A source code minimum initialProfile).WinsPlay play)
    (n : Nat) (row : PairedEntryRow) : FeasibleProfiledPairedState A :=
  ⟨(play n).2.1.target row,
    (profiledGuardedFirstLeft_targetsSafe_of_wins A source code minimum
      initialProfile play hwin n row).2⟩

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledGuardedFirstLeft_overlap_of_wins
    (source : ProfiledGuardedLeftEntrySource A)
    (code : A.State × A.State) (minimum : A.State)
    (initialProfile : LeftInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (play : Nat → RealizedBlockRound In₁ In₂
      (ProfiledLeftReceiverOutput A) Out₂)
    (hwin : (profiledGuardedFirstLeftBlockMonitor.{u, v, x, y, s, 1}
      A source code minimum initialProfile).WinsPlay play)
    (n : Nat) (row : PairedEntryRow)
    (expected : RightInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (hpending :
      ((profiledGuardedFirstLeftBlockMonitor.{u, v, x, y, s, 1}
        A source code minimum initialProfile).run play n).2.2.1 row =
          some expected) :
    pairedLeftClosingForRow row (play n).2.1.physical =
      expected ((play n).1.2, (play n).1.1) := by
  classical
  have hsafeNext := profiledGuardedFirstLeft_safe_of_wins A source code
    minimum initialProfile play hwin (n + 1)
  rw [BlockRecordMonitor.run] at hsafeNext
  simp only [profiledGuardedFirstLeftBlockMonitor, Bool.and_eq_true,
    decide_eq_true_eq] at hsafeNext
  exact hsafeNext.1.2 row expected hpending

end

end


end DetParityAutomaton

end DistributedSynthesis
