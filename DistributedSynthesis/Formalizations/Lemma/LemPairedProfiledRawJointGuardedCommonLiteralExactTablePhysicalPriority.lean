/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedFirstPhysicalPriority
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralExactTailHandoff
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralExactMirrorSeam
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralHeterogeneousTailAcceptance

/-!
# Physical priority of the exact active seam-table projections

The exact (`true`) projection of each heterogeneous seam table is still the
actual narrowed table play; only the proof-side product receiver coordinate
is forgotten.  After erasing its finite first-letter guard, the generic
guarded-first physical-priority theorem applies directly.  Thus the emitted
target thread priority is the minimum priority of the literal physical prefix
of the same table play.  No independently selected policy-bank record list is
mentioned.
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

variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))

/-! ## The code-erased table members

The heterogeneous table may be reached with either internal member.  The
`false` projection is checked by the ordinary physical-sibling monitor, whose
target projection is already the profiled thread root carried by the active
slot.  Hence it enjoys the same pointwise physical-priority law as the exact
projection below. -/

/-- Right seam, code-erased member: its active right slot carries the minimum
priority of the literal strict-left prefix emitted by that same play. -/
theorem
    exists_profiledRawJointLiteralRightBothExactFalsePlay_targetThreadPriority_eq_blockMin
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (env : Nat → In₁ × In₂) (n : Nat) (row : PairedEntryRow) :
    let descriptor :=
      profiledRawJointHybridExactLeftUniformDescriptor A strategy hwin
        installed
    let play := profiledRawJointLiteralRightBothExactFalsePlay A strategy hwin
      installed env
    ∃ slot : ProfiledRawRightSlot A,
      ((play n).2.1.target row).family.right () = some slot ∧
        profiledRawJointThreadRootPriority A (.inl slot) =
          A.priority
            (blockMinState A
              (pairedCodeStateForRow A row descriptor.source.1.1)
              (profiledRawJointTargetLeftPhysicalPrefixRecords A row
                (omegaPrefix play n))) := by
  classical
  dsimp only
  let descriptor :=
    profiledRawJointHybridExactLeftUniformDescriptor A strategy hwin installed
  let play := profiledRawJointLiteralRightBothExactFalsePlay A strategy hwin
    installed env
  have hwins :
      (profiledRawJointLeftPhysicalSiblingMonitor A descriptor false).WinsPlay
        play := by
    simpa [descriptor, play] using
      (profiledRawJointLiteralRightBothExactFalsePlay_wins A strategy hwin
        installed env)
  have hallowed :=
    (profiledRawJointTargetLeft_targetsSafe_of_wins A
      (profiledRawJointUnitLeftTargetProjection A)
      (profiledRawJointLeftPhysicalSiblingAllowed A descriptor)
      descriptor.source play hwins n row).2
  change decide (∃ row' past input,
    (profiledRawJointGuardedFirstLeftTarget A strategy
      (installed.world.oneSidedState A .left)
      (profiledRawJointHybridExactLeftRootPredicate A installed)
      (profiledRawJointHybridExactLeftPolicy A hwin installed)
      row' past input).1 = (play n).2.1.target row) = true at hallowed
  rcases of_decide_eq_true hallowed with ⟨row', past, input, htarget⟩
  let activation := profiledRawJointHybridExactLeftActivation A hwin installed
  let slot := profiledRawLeftChildSlot A descriptor.source activation.lambda
    row' past input
  have hslot : ((play n).2.1.target row).family.right () = some slot := by
    rw [← htarget]
    simpa [slot, activation, descriptor] using
      (activation.target_active_slot row' past input)
  refine ⟨slot, hslot, ?_⟩
  have hpriority :=
    profiledRawJointTargetLeft_targetPriority_eq_blockMin_of_wins A
      (profiledRawJointUnitLeftTargetProjection A)
      (profiledRawJointLeftPhysicalSiblingAllowed A descriptor)
      descriptor.source play hwins n row
  change
    pairedProfiledEntryPriority A
        (profiledRawJointUnitLeftTargetProjection A ((play n).2.1.target row)) =
      _ at hpriority
  rw [profiledRawJointUnitLeftTargetProjection, hslot] at hpriority
  exact hpriority

/-- Mirror seam, code-erased member. -/
theorem
    exists_profiledRawJointLiteralLeftBothExactFalsePlay_targetThreadPriority_eq_blockMin
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (env : Nat → In₂ × In₁) (n : Nat) (row : PairedEntryRow) :
    let descriptor :=
      profiledRawJointHybridExactRightUniformDescriptor A strategy hwin
        installed
    let play := profiledRawJointLiteralLeftBothExactFalsePlay A strategy hwin
      installed env
    ∃ slot : ProfiledRawLeftSlot A,
      ((play n).2.1.target row).family.left () = some slot ∧
        profiledRawJointThreadRootPriority A (.inr slot) =
          A.priority
            (blockMinState A
              (pairedCodeStateForRow A row descriptor.source.1.1)
              (profiledRawJointTargetRightPhysicalPrefixRecords A row
                (omegaPrefix play n))) := by
  classical
  dsimp only
  let descriptor :=
    profiledRawJointHybridExactRightUniformDescriptor A strategy hwin installed
  let play := profiledRawJointLiteralLeftBothExactFalsePlay A strategy hwin
    installed env
  have hwins :
      (profiledRawJointRightPhysicalSiblingMonitor A descriptor false).WinsPlay
        play := by
    simpa [descriptor, play] using
      (profiledRawJointLiteralLeftBothExactFalsePlay_wins A strategy hwin
        installed env)
  have hallowed :=
    (profiledRawJointTargetRight_targetsSafe_of_wins A
      (profiledRawJointUnitRightTargetProjection A)
      (profiledRawJointRightPhysicalSiblingAllowed A descriptor)
      descriptor.source play hwins n row).2
  change decide (∃ row' past input,
    (profiledRawJointGuardedFirstRightTarget A strategy
      (installed.world.oneSidedState A .right)
      (profiledRawJointHybridExactRightRootPredicate A installed)
      (profiledRawJointHybridExactRightPolicy A hwin installed)
      row' past input).1 = (play n).2.1.target row) = true at hallowed
  rcases of_decide_eq_true hallowed with ⟨row', past, input, htarget⟩
  let activation := profiledRawJointHybridExactRightActivation A hwin installed
  let slot := profiledRawRightChildSlot A descriptor.source activation.lambda
    row' past input
  have hslot : ((play n).2.1.target row).family.left () = some slot := by
    rw [← htarget]
    simpa [slot, activation, descriptor] using
      (activation.target_active_slot row' past input)
  refine ⟨slot, hslot, ?_⟩
  have hpriority :=
    profiledRawJointTargetRight_targetPriority_eq_blockMin_of_wins A
      (profiledRawJointUnitRightTargetProjection A)
      (profiledRawJointRightPhysicalSiblingAllowed A descriptor)
      descriptor.source play hwins n row
  change
    pairedProfiledEntryPriority A
        (profiledRawJointUnitRightTargetProjection A ((play n).2.1.target row)) =
      _ at hpriority
  rw [profiledRawJointUnitRightTargetProjection, hslot] at hpriority
  exact hpriority

/-! ## Right seam: the actual strict-left table play -/

theorem
    exists_profiledRawJointLiteralRightBothExactTruePlay_targetThreadPriority_eq_blockMin
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (env : Nat → In₁ × In₂) (n : Nat) (row : PairedEntryRow) :
    let initial := installed.world.oneSidedState A .left
    let RootPred := profiledRawJointHybridExactLeftRootPredicate A installed
    let package := ProfiledRawJointLiteralExactLeftPackage A strategy hwin
      installed
    let source := installed.world.procTwoSlot A
    let play := profiledRawJointLiteralRightBothExactTruePlay A strategy hwin
      installed env
    ∃ slot : ProfiledRawRightSlot A,
      ((play n).2.1.target row).1.family.right () = some slot ∧
        profiledRawJointThreadRootPriority A (.inl slot) =
          A.priority
            (blockMinState A
              (pairedCodeStateForRow A row source.1.1)
              (profiledRawJointGuardedFirstLeftPhysicalPrefixRecords A row
                (omegaPrefix play n))) := by
  classical
  dsimp only
  let initial := installed.world.oneSidedState A .left
  let RootPred := profiledRawJointHybridExactLeftRootPredicate A installed
  let package := ProfiledRawJointLiteralExactLeftPackage A strategy hwin
    installed
  let source := installed.world.procTwoSlot A
  let base := profiledRawJointGuardedFirstLeftBlockMonitor A strategy initial
    RootPred package source
  let allowed := profiledRawJointHybridExactLeftAllowed A installed package
  let play := profiledRawJointLiteralRightBothExactTruePlay A strategy hwin
    installed env
  have hguard : (base.firstLetterGuard allowed).WinsPlay play := by
    simpa [base, allowed, play, initial, RootPred, package, source] using
      (profiledRawJointLiteralRightBothExactTruePlay_wins A strategy hwin
        installed env)
  have hbase : base.WinsPlay play :=
    BlockRecordMonitor.firstLetterGuard_base_wins_of_wins base allowed play
      hguard
  have hbaseRestart : (base.restartAt base.initial).WinsPlay play := by
    simpa [BlockRecordMonitor.restartAt] using hbase
  have hsafeNext := base.restartAt_safe_of_wins
    (fun state ↦ state.2.2.2.2)
    (by
      intro state round hfalse
      change state.2.2.2.2 = false at hfalse
      change ((state.2.2.2.2 && _ && decide _ && decide _) = false)
      rw [hfalse]
      rfl)
    (by
      intro state hfalse
      change state.2.2.2.2 = false at hfalse
      change (if state.2.2.2.2 then _ else 1) = 1
      rw [hfalse]
      rfl)
    base.initial play hbaseRestart (n + 1)
  rw [BlockRecordMonitor.run] at hsafeNext
  simp only [base, profiledRawJointGuardedFirstLeftBlockMonitor,
    BlockRecordMonitor.restartAt, Bool.and_eq_true, decide_eq_true_eq] at hsafeNext
  have hclose := hsafeNext.2 row
  have hscan : (base.run play n).2.1 =
      ((omegaPrefix play n).map
          (profiledRawJointGuardedFirstLeftPhysicalLetter A)).foldl
        (pairedLeftScanStep A) (pairedLeftScanInitial A source.1.1) := by
    clear hsafeNext hclose
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [BlockRecordMonitor.run]
        change pairedLeftScanStep A ((base.run play n).2.1)
            (profiledRawJointGuardedFirstLeftPhysicalLetter A (play n)) = _
        rw [ih, omegaPrefix_succ, List.map_append, List.foldl_append]
        rfl
  exact
    exists_profiledRawJointGuardedFirstLeftTargetThreadPriority_eq_blockMin_of_close
      A strategy initial RootPred package source play n row
        (base.run play n).2.1 hclose hscan

/-! ## Mirror seam: the actual strict-right table play -/

theorem
    exists_profiledRawJointLiteralLeftBothExactTruePlay_targetThreadPriority_eq_blockMin
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (env : Nat → In₂ × In₁) (n : Nat) (row : PairedEntryRow) :
    let initial := installed.world.oneSidedState A .right
    let RootPred := profiledRawJointHybridExactRightRootPredicate A installed
    let package := ProfiledRawJointLiteralExactRightPackage A strategy hwin
      installed
    let source := installed.world.procOneSlot A
    let play := profiledRawJointLiteralLeftBothExactTruePlay A strategy hwin
      installed env
    ∃ slot : ProfiledRawLeftSlot A,
      ((play n).2.1.target row).1.family.left () = some slot ∧
        profiledRawJointThreadRootPriority A (.inr slot) =
          A.priority
            (blockMinState A
              (pairedCodeStateForRow A row source.1.1)
              (profiledRawJointGuardedFirstRightPhysicalPrefixRecords A row
                (omegaPrefix play n))) := by
  classical
  dsimp only
  let initial := installed.world.oneSidedState A .right
  let RootPred := profiledRawJointHybridExactRightRootPredicate A installed
  let package := ProfiledRawJointLiteralExactRightPackage A strategy hwin
    installed
  let source := installed.world.procOneSlot A
  let base := profiledRawJointGuardedFirstRightBlockMonitor A strategy initial
    RootPred package source
  let allowed := profiledRawJointHybridExactRightAllowed A installed package
  let play := profiledRawJointLiteralLeftBothExactTruePlay A strategy hwin
    installed env
  have hguard : (base.firstLetterGuard allowed).WinsPlay play := by
    simpa [base, allowed, play, initial, RootPred, package, source] using
      (profiledRawJointLiteralLeftBothExactTruePlay_wins A strategy hwin
        installed env)
  have hbase : base.WinsPlay play :=
    BlockRecordMonitor.firstLetterGuard_base_wins_of_wins base allowed play
      hguard
  have hbaseRestart : (base.restartAt base.initial).WinsPlay play := by
    simpa [BlockRecordMonitor.restartAt] using hbase
  have hsafeNext := base.restartAt_safe_of_wins
    (fun state ↦ state.2.2.2.2)
    (by
      intro state round hfalse
      change state.2.2.2.2 = false at hfalse
      change ((state.2.2.2.2 && _ && decide _ && decide _) = false)
      rw [hfalse]
      rfl)
    (by
      intro state hfalse
      change state.2.2.2.2 = false at hfalse
      change (if state.2.2.2.2 then _ else 1) = 1
      rw [hfalse]
      rfl)
    base.initial play hbaseRestart (n + 1)
  rw [BlockRecordMonitor.run] at hsafeNext
  simp only [base, profiledRawJointGuardedFirstRightBlockMonitor,
    BlockRecordMonitor.restartAt, Bool.and_eq_true, decide_eq_true_eq] at hsafeNext
  have hclose := hsafeNext.2 row
  have hscan : (base.run play n).2.1 =
      ((omegaPrefix play n).map
          (profiledRawJointGuardedFirstRightPhysicalLetter A)).foldl
        (pairedRightScanStep A) (pairedRightScanInitial A source.1.1) := by
    clear hsafeNext hclose
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [BlockRecordMonitor.run]
        change pairedRightScanStep A ((base.run play n).2.1)
            (profiledRawJointGuardedFirstRightPhysicalLetter A (play n)) = _
        rw [ih, omegaPrefix_succ, List.map_append, List.foldl_append]
        rfl
  exact
    exists_profiledRawJointGuardedFirstRightTargetThreadPriority_eq_blockMin_of_close
      A strategy initial RootPred package source play n row
        (base.run play n).2.1 hclose hscan

end

end DetParityAutomaton

end DistributedSynthesis
