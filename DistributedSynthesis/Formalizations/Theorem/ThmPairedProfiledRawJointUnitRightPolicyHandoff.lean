/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointUnitRightBlockMonitor

/-!
# Finite policy macros and the raw-joint right-to-left handoff

This file isolates the first local handoff brick after raw-joint block
regularization.  A runtime macro is only a reachable state of the one fixed
finite-code policy together with its active `Unit` slot.  It contains no
graph, orientation, strict-leader bit, semantic history, or raw direction.

For a winning narrowed right block, the sticky monitor proves that every
emitted target is an edge of that same policy and that its projected left
slot is the physical close.  The target therefore packages as a reachable
left macro.  The next monitor state stores precisely that slot's initial
profile.  A future owner and receiver can consequently be initialized from
the *same* returned macro; their common-source equality is definitionally
`rfl` and needs no process-visible side information.

The right-to-left direction is completed here.  The macro definitions and
the abstract `AllowedTarget` staging maps are already symmetric, so the
left-to-right controller theorem can be added without changing this
interface when the left monitor lands.
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

/-! ## Finite reachable macros -/

/-- Reachability in the one fixed finite-child-code policy. -/
abbrev ProfiledRawJointUnitPolicyReachable
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode)
    (state : ProfiledRawJointOneSidedProvenancePolicyState A strategy
      initialCode) : Prop :=
  SourceFreeBeliefFiniteCodePolicyImage.Reachable
    (profiledRawJointOneSidedCodeParityDPA A initialCode)
    initialCode
    (ProfiledRawJointOneSidedProvenanceValid A strategy)
    (profiledRawJointOneSidedNext A)
    policy state

/-- A reachable process-one/right macro.  The slot is duplicated only to
make dependent controller families convenient; `active_slot` proves that it
is exactly the unique slot stored by the finite policy state. -/
structure ProfiledRawJointUnitRightPolicyMacro
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode) where
  state : ProfiledRawJointOneSidedProvenancePolicyState A strategy initialCode
  reachable : ProfiledRawJointUnitPolicyReachable A strategy initialCode
    policy state
  slot : ProfiledRawRightSlot A
  active_slot : state.1.family.right () = some slot

/-- A reachable process-two/left macro. -/
structure ProfiledRawJointUnitLeftPolicyMacro
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode) where
  state : ProfiledRawJointOneSidedProvenancePolicyState A strategy initialCode
  reachable : ProfiledRawJointUnitPolicyReachable A strategy initialCode
    policy state
  slot : ProfiledRawLeftSlot A
  active_slot : state.1.family.left () = some slot

noncomputable instance profiledRawJointUnitRightPolicyMacroFintype
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode) :
    Fintype (ProfiledRawJointUnitRightPolicyMacro A strategy initialCode
      policy) := by
  classical
  let encode := fun entry : ProfiledRawJointUnitRightPolicyMacro A strategy
      initialCode policy ↦ (entry.state, entry.slot)
  exact Fintype.ofInjective encode (by
    intro left right heq
    rcases left with ⟨leftState, leftReachable, leftSlot, leftActive⟩
    rcases right with ⟨rightState, rightReachable, rightSlot, rightActive⟩
    simp only [encode, Prod.mk.injEq] at heq
    rcases heq with ⟨rfl, rfl⟩
    rfl)

noncomputable instance profiledRawJointUnitLeftPolicyMacroFintype
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode) :
    Fintype (ProfiledRawJointUnitLeftPolicyMacro A strategy initialCode
      policy) := by
  classical
  let encode := fun entry : ProfiledRawJointUnitLeftPolicyMacro A strategy
      initialCode policy ↦ (entry.state, entry.slot)
  exact Fintype.ofInjective encode (by
    intro left right heq
    rcases left with ⟨leftState, leftReachable, leftSlot, leftActive⟩
    rcases right with ⟨rightState, rightReachable, rightSlot, rightActive⟩
    simp only [encode, Prod.mk.injEq] at heq
    rcases heq with ⟨rfl, rfl⟩
    rfl)

/-! ## Staging an allowed target -/

/-- An allowed right-to-left edge preserves reachability and packages the
active target slot as the next finite macro. -/
def profiledRawJointUnitStageLeftOfAllowed
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode)
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy initialCode
      policy)
    (target : ProfiledRawJointOneSidedProvenancePolicyState A strategy
      initialCode)
    (slot : ProfiledRawLeftSlot A)
    (hallowed : ProfiledRawJointOneSidedProvenanceAllowedTarget A strategy
      initialCode policy source.state target)
    (hslot : target.1.family.left () = some slot) :
    ProfiledRawJointUnitLeftPolicyMacro A strategy initialCode policy where
  state := target
  reachable :=
    SourceFreeBeliefFiniteCodePolicyImage.reachable_of_allowedTarget
      (profiledRawJointOneSidedCodeParityDPA A initialCode)
      initialCode
      (ProfiledRawJointOneSidedProvenanceValid A strategy)
      (profiledRawJointOneSidedNext A)
      policy source.reachable hallowed
  slot := slot
  active_slot := hslot

/-- Left-to-right mirror of the abstract staging map. -/
def profiledRawJointUnitStageRightOfAllowed
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode)
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy initialCode
      policy)
    (target : ProfiledRawJointOneSidedProvenancePolicyState A strategy
      initialCode)
    (slot : ProfiledRawRightSlot A)
    (hallowed : ProfiledRawJointOneSidedProvenanceAllowedTarget A strategy
      initialCode policy source.state target)
    (hslot : target.1.family.right () = some slot) :
    ProfiledRawJointUnitRightPolicyMacro A strategy initialCode policy where
  state := target
  reachable :=
    SourceFreeBeliefFiniteCodePolicyImage.reachable_of_allowedTarget
      (profiledRawJointOneSidedCodeParityDPA A initialCode)
      initialCode
      (ProfiledRawJointOneSidedProvenanceValid A strategy)
      (profiledRawJointOneSidedNext A)
      policy source.reachable hallowed
  slot := slot
  active_slot := hslot

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
@[simp] theorem profiledRawJointUnitStageLeftOfAllowed_state
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode)
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy initialCode
      policy)
    (target : ProfiledRawJointOneSidedProvenancePolicyState A strategy
      initialCode)
    (slot : ProfiledRawLeftSlot A)
    (hallowed : ProfiledRawJointOneSidedProvenanceAllowedTarget A strategy
      initialCode policy source.state target)
    (hslot : target.1.family.left () = some slot) :
    (profiledRawJointUnitStageLeftOfAllowed A strategy initialCode policy
      source target slot hallowed hslot).state = target :=
  rfl

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
@[simp] theorem profiledRawJointUnitStageRightOfAllowed_state
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode)
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy initialCode
      policy)
    (target : ProfiledRawJointOneSidedProvenancePolicyState A strategy
      initialCode)
    (slot : ProfiledRawRightSlot A)
    (hallowed : ProfiledRawJointOneSidedProvenanceAllowedTarget A strategy
      initialCode policy source.state target)
    (hslot : target.1.family.right () = some slot) :
    (profiledRawJointUnitStageRightOfAllowed A strategy initialCode policy
      source target slot hallowed hslot).state = target :=
  rfl

/-! ## Inverting a checked physical target -/

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Exact right-close erasure forces the finite policy target to contain a
left slot.  This is the only target-shape inversion needed by staging. -/
theorem exists_profiledRawJointUnitLeftSlot_of_rightTarget_erases_close
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initialCode : ProfiledRawJointIncidenceCode A (I := Unit)}
    (target : ProfiledRawJointOneSidedProvenancePolicyState A strategy
      initialCode)
    (scan : PairedRightScanState A) (row : PairedEntryRow)
    (physical : PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hclose : erasePairedProfiledState A
        (profiledRawJointUnitRightTargetProfiledState A target) =
      pairedRightCloseTarget A scan row physical) :
    ∃ slot : ProfiledRawLeftSlot A,
      target.1.family.left () = some slot := by
  cases hslot : target.1.family.left () with
  | none =>
      simp [profiledRawJointUnitRightTargetProfiledState, hslot,
        erasePairedProfiledState, pairedRightCloseTarget] at hclose
  | some slot =>
      exact ⟨slot, rfl⟩

/-! ## Sticky-monitor soundness -/

section
omit [Inhabited Out₁] [Inhabited Out₂]

/-- Once the raw-joint right monitor becomes unsafe, it remains unsafe. -/
theorem profiledRawJointUnitRightBlockMonitor_safe_false_persists
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode)
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy initialCode
      policy)
    (play : Nat → RealizedBlockRound In₂ In₁
      (ProfiledRawJointUnitRightReceiverOutput A strategy initialCode) Out₁)
    {N : Nat}
    (hfalse : ((profiledRawJointUnitRightBlockMonitor.{u, v, x, y, s, max u v x y s} A strategy initialCode
      policy source.state source.slot).run play N).2.2.2.2 = false) :
    ∀ n, N ≤ n →
      ((profiledRawJointUnitRightBlockMonitor.{u, v, x, y, s, max u v x y s} A strategy initialCode policy
        source.state source.slot).run play n).2.2.2.2 = false := by
  classical
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero => simpa using hfalse
  | succ k ih =>
      rw [Nat.add_succ, BlockRecordMonitor.run]
      simp only [profiledRawJointUnitRightBlockMonitor]
      change
        (((profiledRawJointUnitRightBlockMonitor.{u, v, x, y, s, max u v x y s} A strategy initialCode policy
          source.state source.slot).run play (N + k)).2.2.2.2 && _ &&
            decide _ && decide _) = false
      rw [ih (Nat.le_add_right N k)]
      rfl

/-- Every finite prefix of a winning raw-joint right play is safe. -/
theorem profiledRawJointUnitRightBlockMonitor_safe_of_wins
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode)
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy initialCode
      policy)
    (play : Nat → RealizedBlockRound In₂ In₁
      (ProfiledRawJointUnitRightReceiverOutput A strategy initialCode) Out₁)
    (hwin : (profiledRawJointUnitRightBlockMonitor.{u, v, x, y, s, max u v x y s} A strategy initialCode
      policy source.state source.slot).WinsPlay play)
    (n : Nat) :
    ((profiledRawJointUnitRightBlockMonitor.{u, v, x, y, s, max u v x y s} A strategy initialCode policy
      source.state source.slot).run play n).2.2.2.2 = true := by
  by_contra hnot
  have hfalse :
      ((profiledRawJointUnitRightBlockMonitor.{u, v, x, y, s, max u v x y s} A strategy initialCode policy
        source.state source.slot).run play n).2.2.2.2 = false :=
    Bool.eq_false_of_not_eq_true hnot
  have hpersist :=
    profiledRawJointUnitRightBlockMonitor_safe_false_persists A strategy
      initialCode policy source play hfalse
  have heventual : ∀ k, n ≤ k →
      (profiledRawJointUnitRightBlockMonitor.{u, v, x, y, s, max u v x y s} A strategy initialCode policy
        source.state source.slot).priority
          ((profiledRawJointUnitRightBlockMonitor.{u, v, x, y, s, max u v x y s} A strategy initialCode policy
            source.state source.slot).run play k) = 1 := by
    intro k hk
    have hs := hpersist k hk
    change
      (if ((profiledRawJointUnitRightBlockMonitor.{u, v, x, y, s, max u v x y s} A strategy initialCode policy
        source.state source.slot).run play k).2.2.2.2 then _ else 1) = 1
    rw [hs]
    rfl
  exact not_natSeqMinEvenParity_of_eventually_one _ n heventual hwin

/-- Every target emitted on a winning right play is both the exact physical
close and an edge of the one fixed finite-code policy. -/
theorem profiledRawJointUnitRight_targetsSafe_of_wins
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode)
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy initialCode
      policy)
    (play : Nat → RealizedBlockRound In₂ In₁
      (ProfiledRawJointUnitRightReceiverOutput A strategy initialCode) Out₁)
    (hwin : (profiledRawJointUnitRightBlockMonitor.{u, v, x, y, s, max u v x y s} A strategy initialCode
      policy source.state source.slot).WinsPlay play)
    (n : Nat) :
    ∀ row,
      erasePairedProfiledState A
          (profiledRawJointUnitRightTargetProfiledState A
            ((play n).2.1.target row)) =
        pairedRightCloseTarget A
          (((profiledRawJointUnitRightBlockMonitor.{u, v, x, y, s, max u v x y s} A strategy initialCode
            policy source.state source.slot).run play n).2.1) row
          (profiledRawJointUnitRightPhysicalLetter A (play n)) ∧
      ProfiledRawJointOneSidedProvenanceAllowedTarget A strategy initialCode
        policy source.state ((play n).2.1.target row) := by
  classical
  have hsafeNext :=
    profiledRawJointUnitRightBlockMonitor_safe_of_wins A strategy initialCode
      policy source play hwin (n + 1)
  rw [BlockRecordMonitor.run] at hsafeNext
  simp only [profiledRawJointUnitRightBlockMonitor, Bool.and_eq_true,
    decide_eq_true_eq] at hsafeNext
  exact hsafeNext.2

/-- A winning right letter exposes an actual active left slot in its target. -/
theorem exists_profiledRawJointUnitRight_target_active_slot_of_wins
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode)
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy initialCode
      policy)
    (play : Nat → RealizedBlockRound In₂ In₁
      (ProfiledRawJointUnitRightReceiverOutput A strategy initialCode) Out₁)
    (hwin : (profiledRawJointUnitRightBlockMonitor.{u, v, x, y, s, max u v x y s} A strategy initialCode
      policy source.state source.slot).WinsPlay play)
    (n : Nat) (row : PairedEntryRow) :
    ∃ slot : ProfiledRawLeftSlot A,
      ((play n).2.1.target row).1.family.left () = some slot := by
  exact exists_profiledRawJointUnitLeftSlot_of_rightTarget_erases_close A
    ((play n).2.1.target row)
    (((profiledRawJointUnitRightBlockMonitor.{u, v, x, y, s, max u v x y s} A strategy initialCode policy
      source.state source.slot).run play n).2.1)
    row (profiledRawJointUnitRightPhysicalLetter A (play n))
    (profiledRawJointUnitRight_targetsSafe_of_wins A strategy initialCode
      policy source play hwin n row).1

/-- The target slot's profile is exactly the pending profile stored after
the winning right letter. -/
theorem exists_profiledRawJointUnitRight_target_pending_profile_of_wins
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode)
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy initialCode
      policy)
    (play : Nat → RealizedBlockRound In₂ In₁
      (ProfiledRawJointUnitRightReceiverOutput A strategy initialCode) Out₁)
    (hwin : (profiledRawJointUnitRightBlockMonitor.{u, v, x, y, s, max u v x y s} A strategy initialCode
      policy source.state source.slot).WinsPlay play)
    (n : Nat) (row : PairedEntryRow) :
    ∃ slot : ProfiledRawLeftSlot A,
      ((play n).2.1.target row).1.family.left () = some slot ∧
      ((profiledRawJointUnitRightBlockMonitor.{u, v, x, y, s, max u v x y s} A strategy initialCode policy
        source.state source.slot).run play (n + 1)).2.2.1 row =
          some slot.2 := by
  obtain ⟨slot, hslot⟩ :=
    exists_profiledRawJointUnitRight_target_active_slot_of_wins A strategy
      initialCode policy source play hwin n row
  refine ⟨slot, hslot, ?_⟩
  rw [BlockRecordMonitor.run]
  simp only [profiledRawJointUnitRightBlockMonitor]
  simp [profiledRawJointUnitRightTargetProfiledState, hslot,
    leftProfileOfProfiledState]

end

/-! ## Public narrowed-controller handoff -/

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- A winning narrowed right tree stages a reachable left macro at every
literal controller letter.  This is the complete policy-specific handoff
fact consumed by the local owner/receiver shell. -/
theorem exists_profiledRawJointUnitLeftPolicyMacro_of_rightNarrowed
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode)
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy initialCode
      policy)
    (narrowed : LabeledTree In₁
      (NarrowedBlockLabel In₂ In₁
        (ProfiledRawJointUnitRightReceiverOutput A strategy initialCode)
        Out₁
        (profiledRawJointUnitRightBlockMonitor.{u, v, x, y, s, max u v x y s} A strategy initialCode policy
          source.state source.slot).State))
    (hthreads : NarrowedAllThreadsWin
      (profiledRawJointUnitRightBlockMonitor.{u, v, x, y, s, max u v x y s} A strategy initialCode policy
        source.state source.slot) narrowed)
    (env : Nat → In₂ × In₁) (n : Nat) (row : PairedEntryRow) :
    let monitor := profiledRawJointUnitRightBlockMonitor.{u, v, x, y, s, max u v x y s} A strategy initialCode
      policy source.state source.slot
    let play := treePlay (narrowedInducedTree monitor narrowed) env
    ∃ target : ProfiledRawJointUnitLeftPolicyMacro A strategy initialCode
        policy,
      target.state = (play n).2.1.target row ∧
        (monitor.run play (n + 1)).2.2.1 row = some target.slot.2 := by
  let monitor := profiledRawJointUnitRightBlockMonitor.{u, v, x, y, s, max u v x y s} A strategy initialCode
    policy source.state source.slot
  let play := treePlay (narrowedInducedTree monitor narrowed) env
  have htree : monitor.lift.WinningTree
      (narrowedInducedTree monitor narrowed) :=
    narrowedInducedTree_winningTree_of_allThreadsWin monitor hthreads
  have hwin : monitor.WinsPlay play :=
    (monitor.lift_winningTree_iff
      (narrowedInducedTree monitor narrowed)).mp htree env
  have hsafe := profiledRawJointUnitRight_targetsSafe_of_wins A strategy
    initialCode policy source play hwin n row
  obtain ⟨slot, hslot, hpending⟩ :=
    exists_profiledRawJointUnitRight_target_pending_profile_of_wins A strategy
      initialCode policy source play hwin n row
  let target := profiledRawJointUnitStageLeftOfAllowed A strategy initialCode
    policy source ((play n).2.1.target row) slot hsafe.2 hslot
  exact ⟨target, rfl, hpending⟩

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- `TransitionRationalTree` specialization of the public handoff theorem. -/
theorem exists_profiledRawJointUnitLeftPolicyMacro_of_rightController
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode)
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy initialCode
      policy)
    (controller : TransitionRationalTree In₁
      (NarrowedBlockLabel In₂ In₁
        (ProfiledRawJointUnitRightReceiverOutput A strategy initialCode)
        Out₁
        (profiledRawJointUnitRightBlockMonitor.{u, v, x, y, s, max u v x y s} A strategy initialCode policy
          source.state source.slot).State))
    (hthreads : NarrowedAllThreadsWin
      (profiledRawJointUnitRightBlockMonitor.{u, v, x, y, s, max u v x y s} A strategy initialCode policy
        source.state source.slot) controller.labeledTree)
    (env : Nat → In₂ × In₁) (n : Nat) (row : PairedEntryRow) :
    let monitor := profiledRawJointUnitRightBlockMonitor.{u, v, x, y, s, max u v x y s} A strategy initialCode
      policy source.state source.slot
    let play := treePlay
      (narrowedInducedTree monitor controller.labeledTree) env
    ∃ target : ProfiledRawJointUnitLeftPolicyMacro A strategy initialCode
        policy,
      target.state = (play n).2.1.target row ∧
        (monitor.run play (n + 1)).2.2.1 row = some target.slot.2 :=
  exists_profiledRawJointUnitLeftPolicyMacro_of_rightNarrowed A strategy
    initialCode policy source controller.labeledTree hthreads env n row

end

end DetParityAutomaton

end DistributedSynthesis
