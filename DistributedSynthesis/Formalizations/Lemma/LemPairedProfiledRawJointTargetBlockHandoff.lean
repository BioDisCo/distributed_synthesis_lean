/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPersistentRightBlock
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPersistentLeftBlock

/-!
# Generic handoff soundness for target-parametric raw-joint blocks

The target-parametric right and left monitors check two facts at every
letter: the target projects to the literal physical close and it satisfies
the caller's finite `Allowed` relation.  Their sticky safety bit makes these
facts consequences of winning, including for every letter read from a
narrowed finite controller.

This is independent of the representation of targets.  Ordinary hybrid
states and states of a one-shot root-guarded policy use the same theorem.
-/

namespace DistributedSynthesis

universe u v x y s t

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

/-! ## Right blocks -/

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype Out₂]

theorem profiledRawJointTargetRightBlockMonitor_safe_false_persists
    {Target : Type t} [Fintype Target]
    (targetState : Target → PairedProfiledTreeState A)
    (Allowed : Target → Prop)
    (source : ProfiledRawRightSlot A)
    (play : Nat → RealizedBlockRound In₂ In₁
      (ProfiledRawJointTargetRightReceiverOutput
        (Out₁ := Out₁) (Out₂ := Out₂) Target) Out₁)
    {N : Nat}
    (hfalse : ((profiledRawJointTargetRightBlockMonitor A Target targetState
      Allowed source).run play N).2.2.2.2 = false) :
    ∀ n, N ≤ n →
      ((profiledRawJointTargetRightBlockMonitor A Target targetState Allowed
        source).run play n).2.2.2.2 = false := by
  classical
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero => simpa using hfalse
  | succ k ih =>
      rw [Nat.add_succ, BlockRecordMonitor.run]
      simp only [profiledRawJointTargetRightBlockMonitor]
      change
        (((profiledRawJointTargetRightBlockMonitor A Target targetState Allowed
          source).run play (N + k)).2.2.2.2 && _ && decide _ && decide _) =
          false
      rw [ih (Nat.le_add_right N k)]
      rfl

theorem profiledRawJointTargetRightBlockMonitor_safe_of_wins
    {Target : Type t} [Fintype Target]
    (targetState : Target → PairedProfiledTreeState A)
    (Allowed : Target → Prop)
    (source : ProfiledRawRightSlot A)
    (play : Nat → RealizedBlockRound In₂ In₁
      (ProfiledRawJointTargetRightReceiverOutput
        (Out₁ := Out₁) (Out₂ := Out₂) Target) Out₁)
    (hwin : (profiledRawJointTargetRightBlockMonitor A Target targetState
      Allowed source).WinsPlay play)
    (n : Nat) :
    ((profiledRawJointTargetRightBlockMonitor A Target targetState Allowed
      source).run play n).2.2.2.2 = true := by
  by_contra hnot
  have hfalse :
      ((profiledRawJointTargetRightBlockMonitor A Target targetState Allowed
        source).run play n).2.2.2.2 = false :=
    Bool.eq_false_of_not_eq_true hnot
  have hpersist :=
    profiledRawJointTargetRightBlockMonitor_safe_false_persists A targetState
      Allowed source play hfalse
  have heventual : ∀ k, n ≤ k →
      (profiledRawJointTargetRightBlockMonitor A Target targetState Allowed
        source).priority
          ((profiledRawJointTargetRightBlockMonitor A Target targetState
            Allowed source).run play k) = 1 := by
    intro k hk
    have hs := hpersist k hk
    change
      (if ((profiledRawJointTargetRightBlockMonitor A Target targetState
        Allowed source).run play k).2.2.2.2 then _ else 1) = 1
    rw [hs]
    rfl
  exact not_natSeqMinEvenParity_of_eventually_one _ n heventual hwin

/-- Every target emitted on a winning target-parametric right play is the
literal physical close and satisfies the caller's allowed relation. -/
theorem profiledRawJointTargetRight_targetsSafe_of_wins
    {Target : Type t} [Fintype Target]
    (targetState : Target → PairedProfiledTreeState A)
    (Allowed : Target → Prop)
    (source : ProfiledRawRightSlot A)
    (play : Nat → RealizedBlockRound In₂ In₁
      (ProfiledRawJointTargetRightReceiverOutput
        (Out₁ := Out₁) (Out₂ := Out₂) Target) Out₁)
    (hwin : (profiledRawJointTargetRightBlockMonitor A Target targetState
      Allowed source).WinsPlay play)
    (n : Nat) : ∀ row,
      erasePairedProfiledState A (targetState ((play n).2.1.target row)) =
          pairedRightCloseTarget A
            (((profiledRawJointTargetRightBlockMonitor A Target targetState
              Allowed source).run play n).2.1) row
            (profiledRawJointTargetRightPhysicalLetter A (play n)) ∧
        Allowed ((play n).2.1.target row) := by
  classical
  have hsafeNext :=
    profiledRawJointTargetRightBlockMonitor_safe_of_wins A targetState Allowed
      source play hwin (n + 1)
  rw [BlockRecordMonitor.run] at hsafeNext
  simp only [profiledRawJointTargetRightBlockMonitor, Bool.and_eq_true,
    decide_eq_true_eq] at hsafeNext
  exact hsafeNext.2

end

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- The same fact for every concrete letter of a winning narrowed right
controller. -/
theorem profiledRawJointTargetRight_narrowedTargetSafe
    {Target : Type t} [Fintype Target]
    (targetState : Target → PairedProfiledTreeState A)
    (Allowed : Target → Prop)
    (source : ProfiledRawRightSlot A)
    (narrowed : LabeledTree In₁
      (NarrowedBlockLabel In₂ In₁
        (ProfiledRawJointTargetRightReceiverOutput
          (Out₁ := Out₁) (Out₂ := Out₂) Target)
        Out₁
        (profiledRawJointTargetRightBlockMonitor A Target targetState Allowed
          source).State))
    (hthreads : NarrowedAllThreadsWin
      (profiledRawJointTargetRightBlockMonitor A Target targetState Allowed
        source) narrowed)
    (env : Nat → In₂ × In₁) (n : Nat) (row : PairedEntryRow) :
    let monitor := profiledRawJointTargetRightBlockMonitor A Target targetState
      Allowed source
    let play := treePlay (narrowedInducedTree monitor narrowed) env
    erasePairedProfiledState A (targetState ((play n).2.1.target row)) =
        pairedRightCloseTarget A ((monitor.run play n).2.1) row
          (profiledRawJointTargetRightPhysicalLetter A (play n)) ∧
      Allowed ((play n).2.1.target row) := by
  let monitor := profiledRawJointTargetRightBlockMonitor A Target targetState
    Allowed source
  let tree := narrowedInducedTree monitor narrowed
  have htree : monitor.lift.WinningTree tree :=
    narrowedInducedTree_winningTree_of_allThreadsWin monitor hthreads
  have hplay : monitor.WinsPlay (treePlay tree env) :=
    (monitor.lift_winningTree_iff tree).mp htree env
  exact profiledRawJointTargetRight_targetsSafe_of_wins A targetState Allowed
    source (treePlay tree env) hplay n row

/-! ## Left blocks -/

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype Out₁]

theorem profiledRawJointTargetLeftBlockMonitor_safe_false_persists
    {Target : Type t} [Fintype Target]
    (targetState : Target → PairedProfiledTreeState A)
    (Allowed : Target → Prop)
    (source : ProfiledRawLeftSlot A)
    (play : Nat → RealizedBlockRound In₁ In₂
      (ProfiledRawJointTargetLeftReceiverOutput
        (Out₁ := Out₁) (Out₂ := Out₂) Target) Out₂)
    {N : Nat}
    (hfalse : ((profiledRawJointTargetLeftBlockMonitor A Target targetState
      Allowed source).run play N).2.2.2.2 = false) :
    ∀ n, N ≤ n →
      ((profiledRawJointTargetLeftBlockMonitor A Target targetState Allowed
        source).run play n).2.2.2.2 = false := by
  classical
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero => simpa using hfalse
  | succ k ih =>
      rw [Nat.add_succ, BlockRecordMonitor.run]
      simp only [profiledRawJointTargetLeftBlockMonitor]
      change
        (((profiledRawJointTargetLeftBlockMonitor A Target targetState Allowed
          source).run play (N + k)).2.2.2.2 && _ && decide _ && decide _) =
          false
      rw [ih (Nat.le_add_right N k)]
      rfl

theorem profiledRawJointTargetLeftBlockMonitor_safe_of_wins
    {Target : Type t} [Fintype Target]
    (targetState : Target → PairedProfiledTreeState A)
    (Allowed : Target → Prop)
    (source : ProfiledRawLeftSlot A)
    (play : Nat → RealizedBlockRound In₁ In₂
      (ProfiledRawJointTargetLeftReceiverOutput
        (Out₁ := Out₁) (Out₂ := Out₂) Target) Out₂)
    (hwin : (profiledRawJointTargetLeftBlockMonitor A Target targetState
      Allowed source).WinsPlay play)
    (n : Nat) :
    ((profiledRawJointTargetLeftBlockMonitor A Target targetState Allowed
      source).run play n).2.2.2.2 = true := by
  by_contra hnot
  have hfalse :
      ((profiledRawJointTargetLeftBlockMonitor A Target targetState Allowed
        source).run play n).2.2.2.2 = false :=
    Bool.eq_false_of_not_eq_true hnot
  have hpersist :=
    profiledRawJointTargetLeftBlockMonitor_safe_false_persists A targetState
      Allowed source play hfalse
  have heventual : ∀ k, n ≤ k →
      (profiledRawJointTargetLeftBlockMonitor A Target targetState Allowed
        source).priority
          ((profiledRawJointTargetLeftBlockMonitor A Target targetState Allowed
            source).run play k) = 1 := by
    intro k hk
    have hs := hpersist k hk
    change
      (if ((profiledRawJointTargetLeftBlockMonitor A Target targetState Allowed
        source).run play k).2.2.2.2 then _ else 1) = 1
    rw [hs]
    rfl
  exact not_natSeqMinEvenParity_of_eventually_one _ n heventual hwin

theorem profiledRawJointTargetLeft_targetsSafe_of_wins
    {Target : Type t} [Fintype Target]
    (targetState : Target → PairedProfiledTreeState A)
    (Allowed : Target → Prop)
    (source : ProfiledRawLeftSlot A)
    (play : Nat → RealizedBlockRound In₁ In₂
      (ProfiledRawJointTargetLeftReceiverOutput
        (Out₁ := Out₁) (Out₂ := Out₂) Target) Out₂)
    (hwin : (profiledRawJointTargetLeftBlockMonitor A Target targetState
      Allowed source).WinsPlay play)
    (n : Nat) : ∀ row,
      erasePairedProfiledState A (targetState ((play n).2.1.target row)) =
          pairedLeftCloseTarget A
            (((profiledRawJointTargetLeftBlockMonitor A Target targetState
              Allowed source).run play n).2.1) row
            (profiledRawJointTargetLeftPhysicalLetter A (play n)) ∧
        Allowed ((play n).2.1.target row) := by
  classical
  have hsafeNext :=
    profiledRawJointTargetLeftBlockMonitor_safe_of_wins A targetState Allowed
      source play hwin (n + 1)
  rw [BlockRecordMonitor.run] at hsafeNext
  simp only [profiledRawJointTargetLeftBlockMonitor, Bool.and_eq_true,
    decide_eq_true_eq] at hsafeNext
  exact hsafeNext.2

end

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledRawJointTargetLeft_narrowedTargetSafe
    {Target : Type t} [Fintype Target]
    (targetState : Target → PairedProfiledTreeState A)
    (Allowed : Target → Prop)
    (source : ProfiledRawLeftSlot A)
    (narrowed : LabeledTree In₂
      (NarrowedBlockLabel In₁ In₂
        (ProfiledRawJointTargetLeftReceiverOutput
          (Out₁ := Out₁) (Out₂ := Out₂) Target)
        Out₂
        (profiledRawJointTargetLeftBlockMonitor A Target targetState Allowed
          source).State))
    (hthreads : NarrowedAllThreadsWin
      (profiledRawJointTargetLeftBlockMonitor A Target targetState Allowed
        source) narrowed)
    (env : Nat → In₁ × In₂) (n : Nat) (row : PairedEntryRow) :
    let monitor := profiledRawJointTargetLeftBlockMonitor A Target targetState
      Allowed source
    let play := treePlay (narrowedInducedTree monitor narrowed) env
    erasePairedProfiledState A (targetState ((play n).2.1.target row)) =
        pairedLeftCloseTarget A ((monitor.run play n).2.1) row
          (profiledRawJointTargetLeftPhysicalLetter A (play n)) ∧
      Allowed ((play n).2.1.target row) := by
  let monitor := profiledRawJointTargetLeftBlockMonitor A Target targetState
    Allowed source
  let tree := narrowedInducedTree monitor narrowed
  have htree : monitor.lift.WinningTree tree :=
    narrowedInducedTree_winningTree_of_allThreadsWin monitor hthreads
  have hplay : monitor.WinsPlay (treePlay tree env) :=
    (monitor.lift_winningTree_iff tree).mp htree env
  exact profiledRawJointTargetLeft_targetsSafe_of_wins A targetState Allowed
    source (treePlay tree env) hplay n row

end

end DetParityAutomaton

end DistributedSynthesis
