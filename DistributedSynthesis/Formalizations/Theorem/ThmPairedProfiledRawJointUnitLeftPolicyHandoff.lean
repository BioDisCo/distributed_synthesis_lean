/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointUnitRightPolicyHandoff
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointUnitLeftBlockMonitor

/-!
# Raw-joint left-to-right policy handoff

This is the exact mirror of the right-to-left handoff.  A winning narrowed
left controller emits an allowed policy target with an active right slot;
the next monitor state stores that slot's profile.  The target is therefore
a finite reachable right macro from which both local roles can restart.
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

/-! ## Inverting a checked left target -/

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Exact left-close erasure forces the finite policy target to contain a
right slot. -/
theorem exists_profiledRawJointUnitRightSlot_of_leftTarget_erases_close
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initialCode : ProfiledRawJointIncidenceCode A (I := Unit)}
    (target : ProfiledRawJointOneSidedProvenancePolicyState A strategy
      initialCode)
    (scan : PairedLeftScanState A) (row : PairedEntryRow)
    (physical : PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hclose : erasePairedProfiledState A
        (profiledRawJointUnitLeftTargetProfiledState A target) =
      pairedLeftCloseTarget A scan row physical) :
    ∃ slot : ProfiledRawRightSlot A,
      target.1.family.right () = some slot := by
  cases hslot : target.1.family.right () with
  | none =>
      simp [profiledRawJointUnitLeftTargetProfiledState, hslot,
        erasePairedProfiledState, pairedLeftCloseTarget] at hclose
  | some slot =>
      exact ⟨slot, rfl⟩

/-! ## Sticky-monitor soundness -/

section
omit [Inhabited Out₁] [Inhabited Out₂]

/-- Once the raw-joint left monitor becomes unsafe, it remains unsafe. -/
theorem profiledRawJointUnitLeftBlockMonitor_safe_false_persists
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode)
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy initialCode
      policy)
    (play : Nat → RealizedBlockRound In₁ In₂
      (ProfiledRawJointUnitLeftReceiverOutput A strategy initialCode) Out₂)
    {N : Nat}
    (hfalse :
      ((profiledRawJointUnitLeftBlockMonitor.{u, v, x, y, s, max u v x y s} A strategy
        initialCode policy source.state source.slot).run play N).2.2.2.2 =
          false) :
    ∀ n, N ≤ n →
      ((profiledRawJointUnitLeftBlockMonitor.{u, v, x, y, s, max u v x y s} A strategy
        initialCode policy source.state source.slot).run play n).2.2.2.2 =
          false := by
  classical
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero => simpa using hfalse
  | succ k ih =>
      rw [Nat.add_succ, BlockRecordMonitor.run]
      simp only [profiledRawJointUnitLeftBlockMonitor]
      change
        (((profiledRawJointUnitLeftBlockMonitor.{u, v, x, y, s, max u v x y s} A strategy
          initialCode policy source.state source.slot).run play
            (N + k)).2.2.2.2 && _ && decide _ && decide _) = false
      rw [ih (Nat.le_add_right N k)]
      rfl

/-- Every finite prefix of a winning raw-joint left play is safe. -/
theorem profiledRawJointUnitLeftBlockMonitor_safe_of_wins
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode)
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy initialCode
      policy)
    (play : Nat → RealizedBlockRound In₁ In₂
      (ProfiledRawJointUnitLeftReceiverOutput A strategy initialCode) Out₂)
    (hwin :
      (profiledRawJointUnitLeftBlockMonitor.{u, v, x, y, s, max u v x y s} A strategy
        initialCode policy source.state source.slot).WinsPlay play)
    (n : Nat) :
    ((profiledRawJointUnitLeftBlockMonitor.{u, v, x, y, s, max u v x y s} A strategy
      initialCode policy source.state source.slot).run play n).2.2.2.2 =
        true := by
  by_contra hnot
  have hfalse :
      ((profiledRawJointUnitLeftBlockMonitor.{u, v, x, y, s, max u v x y s} A strategy
        initialCode policy source.state source.slot).run play n).2.2.2.2 =
          false := Bool.eq_false_of_not_eq_true hnot
  have hpersist :=
    profiledRawJointUnitLeftBlockMonitor_safe_false_persists A strategy
      initialCode policy source play hfalse
  have heventual : ∀ k, n ≤ k →
      (profiledRawJointUnitLeftBlockMonitor.{u, v, x, y, s, max u v x y s} A strategy
        initialCode policy source.state source.slot).priority
          ((profiledRawJointUnitLeftBlockMonitor.{u, v, x, y, s, max u v x y s} A
            strategy initialCode policy source.state source.slot).run play k) =
              1 := by
    intro k hk
    have hs := hpersist k hk
    change
      (if ((profiledRawJointUnitLeftBlockMonitor.{u, v, x, y, s, max u v x y s} A
        strategy initialCode policy source.state source.slot).run play
          k).2.2.2.2 then _ else 1) = 1
    rw [hs]
    rfl
  exact not_natSeqMinEvenParity_of_eventually_one _ n heventual hwin

/-- Every target emitted on a winning left play is both the exact physical
close and an edge of the one fixed finite-code policy. -/
theorem profiledRawJointUnitLeft_targetsSafe_of_wins
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode)
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy initialCode
      policy)
    (play : Nat → RealizedBlockRound In₁ In₂
      (ProfiledRawJointUnitLeftReceiverOutput A strategy initialCode) Out₂)
    (hwin :
      (profiledRawJointUnitLeftBlockMonitor.{u, v, x, y, s, max u v x y s} A strategy
        initialCode policy source.state source.slot).WinsPlay play)
    (n : Nat) :
    ∀ row,
      erasePairedProfiledState A
          (profiledRawJointUnitLeftTargetProfiledState A
            ((play n).2.1.target row)) =
        pairedLeftCloseTarget A
          (((profiledRawJointUnitLeftBlockMonitor.{u, v, x, y, s, max u v x y s} A
            strategy initialCode policy source.state source.slot).run play
              n).2.1) row
          (profiledRawJointUnitLeftPhysicalLetter A (play n)) ∧
      ProfiledRawJointOneSidedProvenanceAllowedTarget A strategy initialCode
        policy source.state ((play n).2.1.target row) := by
  classical
  have hsafeNext :=
    profiledRawJointUnitLeftBlockMonitor_safe_of_wins A strategy initialCode
      policy source play hwin (n + 1)
  rw [BlockRecordMonitor.run] at hsafeNext
  simp only [profiledRawJointUnitLeftBlockMonitor, Bool.and_eq_true,
    decide_eq_true_eq] at hsafeNext
  exact hsafeNext.2

/-- A winning left letter exposes an actual active right slot in its target. -/
theorem exists_profiledRawJointUnitLeft_target_active_slot_of_wins
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode)
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy initialCode
      policy)
    (play : Nat → RealizedBlockRound In₁ In₂
      (ProfiledRawJointUnitLeftReceiverOutput A strategy initialCode) Out₂)
    (hwin :
      (profiledRawJointUnitLeftBlockMonitor.{u, v, x, y, s, max u v x y s} A strategy
        initialCode policy source.state source.slot).WinsPlay play)
    (n : Nat) (row : PairedEntryRow) :
    ∃ slot : ProfiledRawRightSlot A,
      ((play n).2.1.target row).1.family.right () = some slot := by
  exact exists_profiledRawJointUnitRightSlot_of_leftTarget_erases_close A
    ((play n).2.1.target row)
    (((profiledRawJointUnitLeftBlockMonitor.{u, v, x, y, s, max u v x y s} A strategy
      initialCode policy source.state source.slot).run play n).2.1)
    row (profiledRawJointUnitLeftPhysicalLetter A (play n))
    (profiledRawJointUnitLeft_targetsSafe_of_wins A strategy initialCode
      policy source play hwin n row).1

/-- The target slot's profile is exactly the pending profile stored after
the winning left letter. -/
theorem exists_profiledRawJointUnitLeft_target_pending_profile_of_wins
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode)
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy initialCode
      policy)
    (play : Nat → RealizedBlockRound In₁ In₂
      (ProfiledRawJointUnitLeftReceiverOutput A strategy initialCode) Out₂)
    (hwin :
      (profiledRawJointUnitLeftBlockMonitor.{u, v, x, y, s, max u v x y s} A strategy
        initialCode policy source.state source.slot).WinsPlay play)
    (n : Nat) (row : PairedEntryRow) :
    ∃ slot : ProfiledRawRightSlot A,
      ((play n).2.1.target row).1.family.right () = some slot ∧
      ((profiledRawJointUnitLeftBlockMonitor.{u, v, x, y, s, max u v x y s} A strategy
        initialCode policy source.state source.slot).run play
          (n + 1)).2.2.1 row = some slot.2 := by
  obtain ⟨slot, hslot⟩ :=
    exists_profiledRawJointUnitLeft_target_active_slot_of_wins A strategy
      initialCode policy source play hwin n row
  refine ⟨slot, hslot, ?_⟩
  rw [BlockRecordMonitor.run]
  simp only [profiledRawJointUnitLeftBlockMonitor]
  simp [profiledRawJointUnitLeftTargetProfiledState, hslot,
    rightProfileOfProfiledState]

end

/-! ## Public narrowed-controller handoff -/

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- A winning narrowed left tree stages a reachable right macro at every
literal controller letter. -/
theorem exists_profiledRawJointUnitRightPolicyMacro_of_leftNarrowed
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode)
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy initialCode
      policy)
    (narrowed : LabeledTree In₂
      (NarrowedBlockLabel In₁ In₂
        (ProfiledRawJointUnitLeftReceiverOutput A strategy initialCode)
        Out₂
        (profiledRawJointUnitLeftBlockMonitor.{u, v, x, y, s, max u v x y s} A strategy
          initialCode policy source.state source.slot).State))
    (hthreads : NarrowedAllThreadsWin
      (profiledRawJointUnitLeftBlockMonitor.{u, v, x, y, s, max u v x y s} A strategy
        initialCode policy source.state source.slot) narrowed)
    (env : Nat → In₁ × In₂) (n : Nat) (row : PairedEntryRow) :
    let monitor :=
      profiledRawJointUnitLeftBlockMonitor.{u, v, x, y, s, max u v x y s} A strategy
        initialCode policy source.state source.slot
    let play := treePlay (narrowedInducedTree monitor narrowed) env
    ∃ target : ProfiledRawJointUnitRightPolicyMacro A strategy initialCode
        policy,
      target.state = (play n).2.1.target row ∧
        (monitor.run play (n + 1)).2.2.1 row = some target.slot.2 := by
  let monitor :=
    profiledRawJointUnitLeftBlockMonitor.{u, v, x, y, s, max u v x y s} A strategy
      initialCode policy source.state source.slot
  let play := treePlay (narrowedInducedTree monitor narrowed) env
  have htree : monitor.lift.WinningTree
      (narrowedInducedTree monitor narrowed) :=
    narrowedInducedTree_winningTree_of_allThreadsWin monitor hthreads
  have hwin : monitor.WinsPlay play :=
    (monitor.lift_winningTree_iff
      (narrowedInducedTree monitor narrowed)).mp htree env
  have hsafe := profiledRawJointUnitLeft_targetsSafe_of_wins A strategy
    initialCode policy source play hwin n row
  obtain ⟨slot, hslot, hpending⟩ :=
    exists_profiledRawJointUnitLeft_target_pending_profile_of_wins A strategy
      initialCode policy source play hwin n row
  let target := profiledRawJointUnitStageRightOfAllowed A strategy initialCode
    policy source ((play n).2.1.target row) slot hsafe.2 hslot
  exact ⟨target, rfl, hpending⟩

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- `TransitionRationalTree` specialization of the left handoff theorem. -/
theorem exists_profiledRawJointUnitRightPolicyMacro_of_leftController
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode)
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy initialCode
      policy)
    (controller : TransitionRationalTree In₂
      (NarrowedBlockLabel In₁ In₂
        (ProfiledRawJointUnitLeftReceiverOutput A strategy initialCode)
        Out₂
        (profiledRawJointUnitLeftBlockMonitor.{u, v, x, y, s, max u v x y s} A strategy
          initialCode policy source.state source.slot).State))
    (hthreads : NarrowedAllThreadsWin
      (profiledRawJointUnitLeftBlockMonitor.{u, v, x, y, s, max u v x y s} A strategy
        initialCode policy source.state source.slot) controller.labeledTree)
    (env : Nat → In₁ × In₂) (n : Nat) (row : PairedEntryRow) :
    let monitor :=
      profiledRawJointUnitLeftBlockMonitor.{u, v, x, y, s, max u v x y s} A strategy
        initialCode policy source.state source.slot
    let play := treePlay
      (narrowedInducedTree monitor controller.labeledTree) env
    ∃ target : ProfiledRawJointUnitRightPolicyMacro A strategy initialCode
        policy,
      target.state = (play n).2.1.target row ∧
        (monitor.run play (n + 1)).2.2.1 row = some target.slot.2 :=
  exists_profiledRawJointUnitRightPolicyMacro_of_leftNarrowed A strategy
    initialCode policy source controller.labeledTree hthreads env n row

end

end DetParityAutomaton

end DistributedSynthesis
