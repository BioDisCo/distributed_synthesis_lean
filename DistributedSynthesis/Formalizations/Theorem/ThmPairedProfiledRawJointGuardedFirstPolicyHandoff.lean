/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointGuardedFirstRightBlockMonitor
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointGuardedFirstLeftBlockMonitor
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointGuardedFirstPolicyRootHandoff

/-!
# Operational handoff below the exceptional raw-joint block

The exceptional controller emits a literal child of the semantic source
selected by root-pinned provenance.  Winning the sticky monitor forces that
child to carry the live slot prescribed by the physical close.  The finite
child-policy bank can therefore be indexed by the emitted child itself, and
its ordinary recurrent macro starts at the literal policy root `run []`.

This file proves the handoff for every output of a winning narrowed
controller, not only for the canonical full-information realizing output.
It also records that the next monitor state contains the profile of the same
macro slot.  No process receives an orientation or strict-leader signal.
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

/-! ## Right exceptional block: sticky safety -/

section
omit [Inhabited Out₁] [Inhabited Out₂]

/-- Once the exceptional right monitor becomes unsafe, it remains unsafe. -/
theorem profiledRawJointGuardedFirstRightBlockMonitor_safe_false_persists
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop)
    (package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred)
    (source : ProfiledRawRightSlot A)
    (play : Nat → RealizedBlockRound In₂ In₁
      (ProfiledRawJointGuardedFirstRightReceiverOutput A strategy initial
        RootPred package) Out₁)
    {N : Nat}
    (hfalse : ((profiledRawJointGuardedFirstRightBlockMonitor.{u, v, x, y, s,
      max u v x y s}
      A strategy initial RootPred package source).run play N).2.2.2.2 = false) :
    ∀ n, N ≤ n →
      ((profiledRawJointGuardedFirstRightBlockMonitor.{u, v, x, y, s,
        max u v x y s}
        A strategy initial RootPred package source).run play n).2.2.2.2 =
          false := by
  classical
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero => simpa using hfalse
  | succ k ih =>
      rw [Nat.add_succ, BlockRecordMonitor.run]
      simp only [profiledRawJointGuardedFirstRightBlockMonitor]
      change
        (((profiledRawJointGuardedFirstRightBlockMonitor.{u, v, x, y, s,
          max u v x y s}
          A strategy initial RootPred package source).run play
            (N + k)).2.2.2.2 && _ && decide _ && decide _) = false
      rw [ih (Nat.le_add_right N k)]
      rfl

/-- Every finite prefix of a winning exceptional right play is safe. -/
theorem profiledRawJointGuardedFirstRightBlockMonitor_safe_of_wins
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop)
    (package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred)
    (source : ProfiledRawRightSlot A)
    (play : Nat → RealizedBlockRound In₂ In₁
      (ProfiledRawJointGuardedFirstRightReceiverOutput A strategy initial
        RootPred package) Out₁)
    (hwin : (profiledRawJointGuardedFirstRightBlockMonitor.{u, v, x, y, s,
      max u v x y s}
      A strategy initial RootPred package source).WinsPlay play)
    (n : Nat) :
    ((profiledRawJointGuardedFirstRightBlockMonitor.{u, v, x, y, s,
      max u v x y s}
      A strategy initial RootPred package source).run play n).2.2.2.2 = true := by
  by_contra hnot
  have hfalse :
      ((profiledRawJointGuardedFirstRightBlockMonitor.{u, v, x, y, s,
        max u v x y s}
        A strategy initial RootPred package source).run play n).2.2.2.2 =
          false := Bool.eq_false_of_not_eq_true hnot
  have hpersist :=
    profiledRawJointGuardedFirstRightBlockMonitor_safe_false_persists
      A strategy initial RootPred package source play hfalse
  have heventual : ∀ k, n ≤ k →
      (profiledRawJointGuardedFirstRightBlockMonitor.{u, v, x, y, s,
        max u v x y s}
        A strategy initial RootPred package source).priority
          ((profiledRawJointGuardedFirstRightBlockMonitor.{u, v, x, y, s,
            max u v x y s}
            A strategy initial RootPred package source).run play k) = 1 := by
    intro k hk
    have hs := hpersist k hk
    change
      (if ((profiledRawJointGuardedFirstRightBlockMonitor.{u, v, x, y, s,
        max u v x y s}
        A strategy initial RootPred package source).run play
          k).2.2.2.2 then _ else 1) = 1
    rw [hs]
    rfl
  exact not_natSeqMinEvenParity_of_eventually_one _ n heventual hwin

/-- Every target emitted on a winning exceptional right play is the exact
physical close. -/
theorem profiledRawJointGuardedFirstRight_targetsSafe_of_wins
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop)
    (package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred)
    (source : ProfiledRawRightSlot A)
    (play : Nat → RealizedBlockRound In₂ In₁
      (ProfiledRawJointGuardedFirstRightReceiverOutput A strategy initial
        RootPred package) Out₁)
    (hwin : (profiledRawJointGuardedFirstRightBlockMonitor.{u, v, x, y, s,
      max u v x y s}
      A strategy initial RootPred package source).WinsPlay play)
    (n : Nat) :
    ∀ row,
      erasePairedProfiledState A
          (profiledRawJointGuardedFirstRightTargetProfiledState A
            ((play n).2.1.target row)) =
        pairedRightCloseTarget A
          (((profiledRawJointGuardedFirstRightBlockMonitor.{u, v, x, y, s,
            max u v x y s}
            A strategy initial RootPred package source).run play n).2.1) row
          (profiledRawJointGuardedFirstRightPhysicalLetter A (play n)) := by
  classical
  have hsafeNext :=
    profiledRawJointGuardedFirstRightBlockMonitor_safe_of_wins
      A strategy initial RootPred package source play hwin (n + 1)
  rw [BlockRecordMonitor.run] at hsafeNext
  simp only [profiledRawJointGuardedFirstRightBlockMonitor,
    Bool.and_eq_true, decide_eq_true_eq] at hsafeNext
  exact hsafeNext.2

/-- A winning exceptional right letter exposes an active left slot. -/
theorem exists_profiledRawJointGuardedFirstRight_target_active_slot_of_wins
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop)
    (package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred)
    (source : ProfiledRawRightSlot A)
    (play : Nat → RealizedBlockRound In₂ In₁
      (ProfiledRawJointGuardedFirstRightReceiverOutput A strategy initial
        RootPred package) Out₁)
    (hwin : (profiledRawJointGuardedFirstRightBlockMonitor.{u, v, x, y, s,
      max u v x y s}
      A strategy initial RootPred package source).WinsPlay play)
    (n : Nat) (row : PairedEntryRow) :
    ∃ slot : ProfiledRawLeftSlot A,
      ((play n).2.1.target row).1.family.left () = some slot := by
  have hclose :=
    profiledRawJointGuardedFirstRight_targetsSafe_of_wins
      A strategy initial RootPred package source play hwin n row
  cases hslot : ((play n).2.1.target row).1.family.left () with
  | none =>
      simp [profiledRawJointGuardedFirstRightTargetProfiledState, hslot,
        erasePairedProfiledState, pairedRightCloseTarget] at hclose
  | some slot =>
      exact ⟨slot, rfl⟩

/-- The active child slot's profile is exactly the pending profile stored
after the winning exceptional right letter. -/
theorem exists_profiledRawJointGuardedFirstRight_target_pending_profile_of_wins
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop)
    (package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred)
    (source : ProfiledRawRightSlot A)
    (play : Nat → RealizedBlockRound In₂ In₁
      (ProfiledRawJointGuardedFirstRightReceiverOutput A strategy initial
        RootPred package) Out₁)
    (hwin : (profiledRawJointGuardedFirstRightBlockMonitor.{u, v, x, y, s,
      max u v x y s}
      A strategy initial RootPred package source).WinsPlay play)
    (n : Nat) (row : PairedEntryRow) :
    ∃ slot : ProfiledRawLeftSlot A,
      ((play n).2.1.target row).1.family.left () = some slot ∧
      ((profiledRawJointGuardedFirstRightBlockMonitor.{u, v, x, y, s,
        max u v x y s}
        A strategy initial RootPred package source).run play
          (n + 1)).2.2.1 row = some slot.2 := by
  obtain ⟨slot, hslot⟩ :=
    exists_profiledRawJointGuardedFirstRight_target_active_slot_of_wins
      A strategy initial RootPred package source play hwin n row
  refine ⟨slot, hslot, ?_⟩
  rw [BlockRecordMonitor.run]
  simp only [profiledRawJointGuardedFirstRightBlockMonitor]
  simp [profiledRawJointGuardedFirstRightTargetProfiledState, hslot,
    leftProfileOfProfiledState]

end

/-! ## Right exceptional block: public root-macro handoff -/

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Every literal target of a winning exceptional right tree initializes the
ordinary left-policy bank at the actual emitted child and at `run []`. -/
theorem exists_profiledRawJointGuardedFirstLeftPolicyRoot_of_rightNarrowed
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hstrategy : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop)
    (package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred)
    (source : ProfiledRawRightSlot A)
    (narrowed : LabeledTree In₁
      (NarrowedBlockLabel In₂ In₁
        (ProfiledRawJointGuardedFirstRightReceiverOutput A strategy initial
          RootPred package) Out₁
        (profiledRawJointGuardedFirstRightBlockMonitor.{u, v, x, y, s,
          max u v x y s} A strategy initial
          RootPred package source).State))
    (hthreads : NarrowedAllThreadsWin
      (profiledRawJointGuardedFirstRightBlockMonitor.{u, v, x, y, s,
        max u v x y s} A strategy initial
        RootPred package source) narrowed)
    (env : Nat → In₂ × In₁) (n : Nat) (row : PairedEntryRow) :
    let selected := profiledRawJointRootPinnedSelectedSource A strategy
      initial RootPred package
    let bank := profiledRawJointRootPinnedLiteralChildPolicyBank A strategy
      hstrategy initial RootPred package
    let monitor := profiledRawJointGuardedFirstRightBlockMonitor.{u, v, x, y,
      s, max u v x y s} A strategy
      initial RootPred package source
    let play := treePlay (narrowedInducedTree monitor narrowed) env
    ∃ (child : ProfiledRawJointOneSidedLiteralChildCode A strategy selected)
        (target : ProfiledRawJointUnitLeftPolicyMacro A strategy child.1
          (bank child)),
      child = (play n).2.1.target row ∧
      target.state = (bank child).run [] ∧
      (monitor.run play (n + 1)).2.2.1 row = some target.slot.2 := by
  let selected := profiledRawJointRootPinnedSelectedSource A strategy
    initial RootPred package
  let bank := profiledRawJointRootPinnedLiteralChildPolicyBank A strategy
    hstrategy initial RootPred package
  let monitor := profiledRawJointGuardedFirstRightBlockMonitor.{u, v, x, y, s,
    max u v x y s} A strategy
    initial RootPred package source
  let play := treePlay (narrowedInducedTree monitor narrowed) env
  have htree : monitor.lift.WinningTree
      (narrowedInducedTree monitor narrowed) :=
    narrowedInducedTree_winningTree_of_allThreadsWin monitor hthreads
  have hwin : monitor.WinsPlay play :=
    (monitor.lift_winningTree_iff
      (narrowedInducedTree monitor narrowed)).mp htree env
  obtain ⟨slot, hslot, hpending⟩ :=
    exists_profiledRawJointGuardedFirstRight_target_pending_profile_of_wins
      A strategy initial RootPred package source play hwin n row
  let child := (play n).2.1.target row
  let target := profiledRawJointLiteralChildLeftPolicyRoot A strategy selected
    bank child slot hslot
  exact ⟨child, target, rfl, rfl, hpending⟩

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- `TransitionRationalTree` specialization of the exceptional right
handoff. -/
theorem exists_profiledRawJointGuardedFirstLeftPolicyRoot_of_rightController
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hstrategy : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop)
    (package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred)
    (source : ProfiledRawRightSlot A)
    (controller : TransitionRationalTree In₁
      (NarrowedBlockLabel In₂ In₁
        (ProfiledRawJointGuardedFirstRightReceiverOutput A strategy initial
          RootPred package) Out₁
        (profiledRawJointGuardedFirstRightBlockMonitor.{u, v, x, y, s,
          max u v x y s} A strategy initial
          RootPred package source).State))
    (hthreads : NarrowedAllThreadsWin
      (profiledRawJointGuardedFirstRightBlockMonitor.{u, v, x, y, s,
        max u v x y s} A strategy initial
        RootPred package source) controller.labeledTree)
    (env : Nat → In₂ × In₁) (n : Nat) (row : PairedEntryRow) :
    let selected := profiledRawJointRootPinnedSelectedSource A strategy
      initial RootPred package
    let bank := profiledRawJointRootPinnedLiteralChildPolicyBank A strategy
      hstrategy initial RootPred package
    let monitor := profiledRawJointGuardedFirstRightBlockMonitor.{u, v, x, y,
      s, max u v x y s} A strategy
      initial RootPred package source
    let play := treePlay
      (narrowedInducedTree monitor controller.labeledTree) env
    ∃ (child : ProfiledRawJointOneSidedLiteralChildCode A strategy selected)
        (target : ProfiledRawJointUnitLeftPolicyMacro A strategy child.1
          (bank child)),
      child = (play n).2.1.target row ∧
      target.state = (bank child).run [] ∧
      (monitor.run play (n + 1)).2.2.1 row = some target.slot.2 :=
  exists_profiledRawJointGuardedFirstLeftPolicyRoot_of_rightNarrowed
    A strategy hstrategy initial RootPred package source controller.labeledTree
      hthreads env n row

/-! ## Left exceptional block: sticky safety -/

section
omit [Inhabited Out₁] [Inhabited Out₂]

/-- Once the exceptional left monitor becomes unsafe, it remains unsafe. -/
theorem profiledRawJointGuardedFirstLeftBlockMonitor_safe_false_persists
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop)
    (package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred)
    (source : ProfiledRawLeftSlot A)
    (play : Nat → RealizedBlockRound In₁ In₂
      (ProfiledRawJointGuardedFirstLeftReceiverOutput A strategy initial
        RootPred package) Out₂)
    {N : Nat}
    (hfalse : ((profiledRawJointGuardedFirstLeftBlockMonitor.{u, v, x, y, s,
      max u v x y s}
      A strategy initial RootPred package source).run play N).2.2.2.2 = false) :
    ∀ n, N ≤ n →
      ((profiledRawJointGuardedFirstLeftBlockMonitor.{u, v, x, y, s,
        max u v x y s}
        A strategy initial RootPred package source).run play n).2.2.2.2 =
          false := by
  classical
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero => simpa using hfalse
  | succ k ih =>
      rw [Nat.add_succ, BlockRecordMonitor.run]
      simp only [profiledRawJointGuardedFirstLeftBlockMonitor]
      change
        (((profiledRawJointGuardedFirstLeftBlockMonitor.{u, v, x, y, s,
          max u v x y s}
          A strategy initial RootPred package source).run play
            (N + k)).2.2.2.2 && _ && decide _ && decide _) = false
      rw [ih (Nat.le_add_right N k)]
      rfl

/-- Every finite prefix of a winning exceptional left play is safe. -/
theorem profiledRawJointGuardedFirstLeftBlockMonitor_safe_of_wins
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop)
    (package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred)
    (source : ProfiledRawLeftSlot A)
    (play : Nat → RealizedBlockRound In₁ In₂
      (ProfiledRawJointGuardedFirstLeftReceiverOutput A strategy initial
        RootPred package) Out₂)
    (hwin : (profiledRawJointGuardedFirstLeftBlockMonitor.{u, v, x, y, s,
      max u v x y s}
      A strategy initial RootPred package source).WinsPlay play)
    (n : Nat) :
    ((profiledRawJointGuardedFirstLeftBlockMonitor.{u, v, x, y, s,
      max u v x y s}
      A strategy initial RootPred package source).run play n).2.2.2.2 = true := by
  by_contra hnot
  have hfalse :
      ((profiledRawJointGuardedFirstLeftBlockMonitor.{u, v, x, y, s,
        max u v x y s}
        A strategy initial RootPred package source).run play n).2.2.2.2 =
          false := Bool.eq_false_of_not_eq_true hnot
  have hpersist :=
    profiledRawJointGuardedFirstLeftBlockMonitor_safe_false_persists
      A strategy initial RootPred package source play hfalse
  have heventual : ∀ k, n ≤ k →
      (profiledRawJointGuardedFirstLeftBlockMonitor.{u, v, x, y, s,
        max u v x y s}
        A strategy initial RootPred package source).priority
          ((profiledRawJointGuardedFirstLeftBlockMonitor.{u, v, x, y, s,
            max u v x y s}
            A strategy initial RootPred package source).run play k) = 1 := by
    intro k hk
    have hs := hpersist k hk
    change
      (if ((profiledRawJointGuardedFirstLeftBlockMonitor.{u, v, x, y, s,
        max u v x y s}
        A strategy initial RootPred package source).run play
          k).2.2.2.2 then _ else 1) = 1
    rw [hs]
    rfl
  exact not_natSeqMinEvenParity_of_eventually_one _ n heventual hwin

/-- Every target emitted on a winning exceptional left play is the exact
physical close. -/
theorem profiledRawJointGuardedFirstLeft_targetsSafe_of_wins
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop)
    (package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred)
    (source : ProfiledRawLeftSlot A)
    (play : Nat → RealizedBlockRound In₁ In₂
      (ProfiledRawJointGuardedFirstLeftReceiverOutput A strategy initial
        RootPred package) Out₂)
    (hwin : (profiledRawJointGuardedFirstLeftBlockMonitor.{u, v, x, y, s,
      max u v x y s}
      A strategy initial RootPred package source).WinsPlay play)
    (n : Nat) :
    ∀ row,
      erasePairedProfiledState A
          (profiledRawJointGuardedFirstLeftTargetProfiledState A
            ((play n).2.1.target row)) =
        pairedLeftCloseTarget A
          (((profiledRawJointGuardedFirstLeftBlockMonitor.{u, v, x, y, s,
            max u v x y s}
            A strategy initial RootPred package source).run play n).2.1) row
          (profiledRawJointGuardedFirstLeftPhysicalLetter A (play n)) := by
  classical
  have hsafeNext :=
    profiledRawJointGuardedFirstLeftBlockMonitor_safe_of_wins
      A strategy initial RootPred package source play hwin (n + 1)
  rw [BlockRecordMonitor.run] at hsafeNext
  simp only [profiledRawJointGuardedFirstLeftBlockMonitor,
    Bool.and_eq_true, decide_eq_true_eq] at hsafeNext
  exact hsafeNext.2

/-- A winning exceptional left letter exposes an active right slot. -/
theorem exists_profiledRawJointGuardedFirstLeft_target_active_slot_of_wins
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop)
    (package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred)
    (source : ProfiledRawLeftSlot A)
    (play : Nat → RealizedBlockRound In₁ In₂
      (ProfiledRawJointGuardedFirstLeftReceiverOutput A strategy initial
        RootPred package) Out₂)
    (hwin : (profiledRawJointGuardedFirstLeftBlockMonitor.{u, v, x, y, s,
      max u v x y s}
      A strategy initial RootPred package source).WinsPlay play)
    (n : Nat) (row : PairedEntryRow) :
    ∃ slot : ProfiledRawRightSlot A,
      ((play n).2.1.target row).1.family.right () = some slot := by
  have hclose :=
    profiledRawJointGuardedFirstLeft_targetsSafe_of_wins
      A strategy initial RootPred package source play hwin n row
  cases hslot : ((play n).2.1.target row).1.family.right () with
  | none =>
      simp [profiledRawJointGuardedFirstLeftTargetProfiledState, hslot,
        erasePairedProfiledState, pairedLeftCloseTarget] at hclose
  | some slot =>
      exact ⟨slot, rfl⟩

/-- The active child slot's profile is exactly the pending profile stored
after the winning exceptional left letter. -/
theorem exists_profiledRawJointGuardedFirstLeft_target_pending_profile_of_wins
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop)
    (package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred)
    (source : ProfiledRawLeftSlot A)
    (play : Nat → RealizedBlockRound In₁ In₂
      (ProfiledRawJointGuardedFirstLeftReceiverOutput A strategy initial
        RootPred package) Out₂)
    (hwin : (profiledRawJointGuardedFirstLeftBlockMonitor.{u, v, x, y, s,
      max u v x y s}
      A strategy initial RootPred package source).WinsPlay play)
    (n : Nat) (row : PairedEntryRow) :
    ∃ slot : ProfiledRawRightSlot A,
      ((play n).2.1.target row).1.family.right () = some slot ∧
      ((profiledRawJointGuardedFirstLeftBlockMonitor.{u, v, x, y, s,
        max u v x y s}
        A strategy initial RootPred package source).run play
          (n + 1)).2.2.1 row = some slot.2 := by
  obtain ⟨slot, hslot⟩ :=
    exists_profiledRawJointGuardedFirstLeft_target_active_slot_of_wins
      A strategy initial RootPred package source play hwin n row
  refine ⟨slot, hslot, ?_⟩
  rw [BlockRecordMonitor.run]
  simp only [profiledRawJointGuardedFirstLeftBlockMonitor]
  simp [profiledRawJointGuardedFirstLeftTargetProfiledState, hslot,
    rightProfileOfProfiledState]

end

/-! ## Left exceptional block: public root-macro handoff -/

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Every literal target of a winning exceptional left tree initializes the
ordinary right-policy bank at the actual emitted child and at `run []`. -/
theorem exists_profiledRawJointGuardedFirstRightPolicyRoot_of_leftNarrowed
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hstrategy : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop)
    (package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred)
    (source : ProfiledRawLeftSlot A)
    (narrowed : LabeledTree In₂
      (NarrowedBlockLabel In₁ In₂
        (ProfiledRawJointGuardedFirstLeftReceiverOutput A strategy initial
          RootPred package) Out₂
        (profiledRawJointGuardedFirstLeftBlockMonitor.{u, v, x, y, s,
          max u v x y s} A strategy initial
          RootPred package source).State))
    (hthreads : NarrowedAllThreadsWin
      (profiledRawJointGuardedFirstLeftBlockMonitor.{u, v, x, y, s,
        max u v x y s} A strategy initial
        RootPred package source) narrowed)
    (env : Nat → In₁ × In₂) (n : Nat) (row : PairedEntryRow) :
    let selected := profiledRawJointRootPinnedSelectedSource A strategy
      initial RootPred package
    let bank := profiledRawJointRootPinnedLiteralChildPolicyBank A strategy
      hstrategy initial RootPred package
    let monitor := profiledRawJointGuardedFirstLeftBlockMonitor.{u, v, x, y,
      s, max u v x y s} A strategy
      initial RootPred package source
    let play := treePlay (narrowedInducedTree monitor narrowed) env
    ∃ (child : ProfiledRawJointOneSidedLiteralChildCode A strategy selected)
        (target : ProfiledRawJointUnitRightPolicyMacro A strategy child.1
          (bank child)),
      child = (play n).2.1.target row ∧
      target.state = (bank child).run [] ∧
      (monitor.run play (n + 1)).2.2.1 row = some target.slot.2 := by
  let selected := profiledRawJointRootPinnedSelectedSource A strategy
    initial RootPred package
  let bank := profiledRawJointRootPinnedLiteralChildPolicyBank A strategy
    hstrategy initial RootPred package
  let monitor := profiledRawJointGuardedFirstLeftBlockMonitor.{u, v, x, y, s,
    max u v x y s} A strategy
    initial RootPred package source
  let play := treePlay (narrowedInducedTree monitor narrowed) env
  have htree : monitor.lift.WinningTree
      (narrowedInducedTree monitor narrowed) :=
    narrowedInducedTree_winningTree_of_allThreadsWin monitor hthreads
  have hwin : monitor.WinsPlay play :=
    (monitor.lift_winningTree_iff
      (narrowedInducedTree monitor narrowed)).mp htree env
  obtain ⟨slot, hslot, hpending⟩ :=
    exists_profiledRawJointGuardedFirstLeft_target_pending_profile_of_wins
      A strategy initial RootPred package source play hwin n row
  let child := (play n).2.1.target row
  let target := profiledRawJointLiteralChildRightPolicyRoot A strategy selected
    bank child slot hslot
  exact ⟨child, target, rfl, rfl, hpending⟩

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- `TransitionRationalTree` specialization of the exceptional left
handoff. -/
theorem exists_profiledRawJointGuardedFirstRightPolicyRoot_of_leftController
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hstrategy : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop)
    (package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred)
    (source : ProfiledRawLeftSlot A)
    (controller : TransitionRationalTree In₂
      (NarrowedBlockLabel In₁ In₂
        (ProfiledRawJointGuardedFirstLeftReceiverOutput A strategy initial
          RootPred package) Out₂
        (profiledRawJointGuardedFirstLeftBlockMonitor.{u, v, x, y, s,
          max u v x y s} A strategy initial
          RootPred package source).State))
    (hthreads : NarrowedAllThreadsWin
      (profiledRawJointGuardedFirstLeftBlockMonitor.{u, v, x, y, s,
        max u v x y s} A strategy initial
        RootPred package source) controller.labeledTree)
    (env : Nat → In₁ × In₂) (n : Nat) (row : PairedEntryRow) :
    let selected := profiledRawJointRootPinnedSelectedSource A strategy
      initial RootPred package
    let bank := profiledRawJointRootPinnedLiteralChildPolicyBank A strategy
      hstrategy initial RootPred package
    let monitor := profiledRawJointGuardedFirstLeftBlockMonitor.{u, v, x, y,
      s, max u v x y s} A strategy
      initial RootPred package source
    let play := treePlay
      (narrowedInducedTree monitor controller.labeledTree) env
    ∃ (child : ProfiledRawJointOneSidedLiteralChildCode A strategy selected)
        (target : ProfiledRawJointUnitRightPolicyMacro A strategy child.1
          (bank child)),
      child = (play n).2.1.target row ∧
      target.state = (bank child).run [] ∧
      (monitor.run play (n + 1)).2.2.1 row = some target.slot.2 :=
  exists_profiledRawJointGuardedFirstRightPolicyRoot_of_leftNarrowed
    A strategy hstrategy initial RootPred package source controller.labeledTree
      hthreads env n row

end

end DetParityAutomaton

end DistributedSynthesis
