/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridFullRestartFirstThenBothReceiverAdapter

/-!
# Finite monitor for the first-then-both restart lane

The full-restart lane consumes `.first` on its first block record and `.both`
thereafter.  This file turns the finite scan and receiver adapter into an
ordinary `BlockRecordMonitor`.  A persistent Boolean records exact target
safety; once a target check fails, priority `1` is emitted forever.  On a
valid semantic play, priority `0` is emitted forever.  Omega acceptance is
provided by the transported existing block monitor; this lane checks only
the finite state and minimum used at an operational close.

This monitor is deliberately separate from the transported two-row monitor.
It proves that the third lane itself is finite and realizable from the exact
source-level extension, without identifying it with either constant row.
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

/-! ## Physical projections -/

/-- Forget all right certificates and retain the physical block letter. -/
def profiledRawJointRightFirstThenBothPhysicalLetter
    {Target : Type t}
    (letter : RealizedBlockRound In₂ In₁
      (ProfiledRawJointRightFirstThenBothReceiverOutput
        (Out₁ := Out₁) (Out₂ := Out₂) Target) Out₁) :
    PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) :=
  profiledRawJointTargetRightPhysicalLetter A
    (letter.1, letter.2.1.base, letter.2.2)

/-- Left physical projection. -/
def profiledRawJointLeftFirstThenBothPhysicalLetter
    {Target : Type t}
    (letter : RealizedBlockRound In₁ In₂
      (ProfiledRawJointLeftFirstThenBothReceiverOutput
        (Out₁ := Out₁) (Out₂ := Out₂) Target) Out₂) :
    PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) :=
  profiledRawJointTargetLeftPhysicalLetter A
    (letter.1, letter.2.1.base, letter.2.2)

/-! ## The two finite monitors -/

/-- Right mixed-lane monitor.  Its state is the exact finite scan together
with a persistent target-safety bit. -/
noncomputable def profiledRawJointRightFirstThenBothMonitor
    (Target : Type t) [Fintype Target]
    (targetState : Target → PairedProfiledTreeState A)
    (Allowed : Target → Prop)
    (code : A.State × A.State) :
    BlockRecordMonitor In₂ In₁
      (ProfiledRawJointRightFirstThenBothReceiverOutput
        (Out₁ := Out₁) (Out₂ := Out₂) Target) Out₁ := by
  classical
  exact {
    State := ProfiledRawJointFirstThenBothScanState A × Bool
    stateFinite := inferInstance
    initial := (profiledRawJointFirstThenBothScanInitial A code, true)
    step := fun monitorState letter ↦
      let physical := profiledRawJointRightFirstThenBothPhysicalLetter A letter
      let targetSafe := ProfiledRawJointRightFirstThenBothTargetSafe A
        targetState Allowed monitorState.1 physical
        letter.2.1.firstThenBothTarget
      (profiledRawJointRightFirstThenBothScanStep A monitorState.1 physical,
        monitorState.2 && decide targetSafe)
    priority := fun monitorState ↦ if monitorState.2 then 0 else 1
  }

/-- Left mixed-lane monitor. -/
noncomputable def profiledRawJointLeftFirstThenBothMonitor
    (Target : Type t) [Fintype Target]
    (targetState : Target → PairedProfiledTreeState A)
    (Allowed : Target → Prop)
    (code : A.State × A.State) :
    BlockRecordMonitor In₁ In₂
      (ProfiledRawJointLeftFirstThenBothReceiverOutput
        (Out₁ := Out₁) (Out₂ := Out₂) Target) Out₂ := by
  classical
  exact {
    State := ProfiledRawJointFirstThenBothScanState A × Bool
    stateFinite := inferInstance
    initial := (profiledRawJointFirstThenBothScanInitial A code, true)
    step := fun monitorState letter ↦
      let physical := profiledRawJointLeftFirstThenBothPhysicalLetter A letter
      let targetSafe := ProfiledRawJointLeftFirstThenBothTargetSafe A
        targetState Allowed monitorState.1 physical
        letter.2.1.firstThenBothTarget
      (profiledRawJointLeftFirstThenBothScanStep A monitorState.1 physical,
        monitorState.2 && decide targetSafe)
    priority := fun monitorState ↦ if monitorState.2 then 0 else 1
  }

/-! ## Semantic play equations -/

theorem profiledRawJointTargetRightFirstThenBoth_pairPlay_eq_letterAt
    {Target : Type t}
    {targetState : Target → PairedProfiledTreeState A}
    {Allowed : Target → Prop}
    {source : ProfiledRawRightSlot A}
    (activation : ProfiledRawJointTargetRightBlockActivation A Target
      targetState Allowed source)
    (extension :
      ProfiledRawJointTargetRightFirstThenBothActivationExtension A activation)
    (env : Nat → In₂ × In₁) (n : Nat) :
    pairPlay
        (profiledRawJointTargetRightFirstThenBothReceiverStrategyOfExtension A
          activation extension)
        (pairedRightSenderStrategy activation.lambda) env n =
      (env n,
        profiledRawJointTargetRightFirstThenBothReceiverStrategyOfExtension A
          activation extension (omegaPrefix env n) (env n),
        activation.lambda.blind (senderWord (omegaPrefix env n)) (env n).2) := by
  rw [pairPlay, treePlay, treeOfPair, branchNode_eq_omegaPrefix]
  simp [blockLabelApply, pairedRightSenderStrategy, senderWord, omegaPrefix]

theorem profiledRawJointTargetLeftFirstThenBoth_pairPlay_eq_letterAt
    {Target : Type t}
    {targetState : Target → PairedProfiledTreeState A}
    {Allowed : Target → Prop}
    {source : ProfiledRawLeftSlot A}
    (activation : ProfiledRawJointTargetLeftBlockActivation A Target
      targetState Allowed source)
    (extension :
      ProfiledRawJointTargetLeftFirstThenBothActivationExtension A activation)
    (env : Nat → In₁ × In₂) (n : Nat) :
    pairPlay
        (profiledRawJointTargetLeftFirstThenBothReceiverStrategyOfExtension A
          activation extension)
        (pairedLeftSenderStrategy activation.lambda) env n =
      (env n,
        profiledRawJointTargetLeftFirstThenBothReceiverStrategyOfExtension A
          activation extension (omegaPrefix env n) (env n),
        activation.lambda.blind (senderWord (omegaPrefix env n)) (env n).2) := by
  rw [pairPlay, treePlay, treeOfPair, branchNode_eq_omegaPrefix]
  simp [blockLabelApply, pairedLeftSenderStrategy, senderWord, omegaPrefix]

theorem profiledRawJointTargetRightFirstThenBoth_pairPlay_physical
    {Target : Type t}
    {targetState : Target → PairedProfiledTreeState A}
    {Allowed : Target → Prop}
    {source : ProfiledRawRightSlot A}
    (activation : ProfiledRawJointTargetRightBlockActivation A Target
      targetState Allowed source)
    (extension :
      ProfiledRawJointTargetRightFirstThenBothActivationExtension A activation)
    (env : Nat → In₂ × In₁) (n : Nat) :
    profiledRawJointRightFirstThenBothPhysicalLetter A
        (pairPlay
          (profiledRawJointTargetRightFirstThenBothReceiverStrategyOfExtension
            A activation extension)
          (pairedRightSenderStrategy activation.lambda) env n) =
      pairedRightBlockWord activation.lambda env n := by
  rw [profiledRawJointTargetRightFirstThenBoth_pairPlay_eq_letterAt A
    activation extension env n]
  simp [profiledRawJointRightFirstThenBothPhysicalLetter,
    profiledRawJointTargetRightFirstThenBothReceiverStrategyOfExtension,
    profiledRawJointTargetRightFirstThenBothReceiverStrategy,
    profiledRawJointTargetRightPhysicalLetter, indexedTargetPhysicalLetter,
    profiledRawJointTargetRightReceiverStrategy, pairedRightReceiverStrategy,
    pairedRightBlockWord, pairedRightBlockLetterAt]

theorem profiledRawJointTargetLeftFirstThenBoth_pairPlay_physical
    {Target : Type t}
    {targetState : Target → PairedProfiledTreeState A}
    {Allowed : Target → Prop}
    {source : ProfiledRawLeftSlot A}
    (activation : ProfiledRawJointTargetLeftBlockActivation A Target
      targetState Allowed source)
    (extension :
      ProfiledRawJointTargetLeftFirstThenBothActivationExtension A activation)
    (env : Nat → In₁ × In₂) (n : Nat) :
    profiledRawJointLeftFirstThenBothPhysicalLetter A
        (pairPlay
          (profiledRawJointTargetLeftFirstThenBothReceiverStrategyOfExtension A
            activation extension)
          (pairedLeftSenderStrategy activation.lambda) env n) =
      pairedLeftBlockWord activation.lambda env n := by
  rw [profiledRawJointTargetLeftFirstThenBoth_pairPlay_eq_letterAt A
    activation extension env n]
  simp [profiledRawJointLeftFirstThenBothPhysicalLetter,
    profiledRawJointTargetLeftFirstThenBothReceiverStrategyOfExtension,
    profiledRawJointTargetLeftFirstThenBothReceiverStrategy,
    profiledRawJointTargetLeftPhysicalLetter, indexedTargetPhysicalLetter,
    profiledRawJointTargetLeftReceiverStrategy, pairedLeftReceiverStrategy,
    pairedLeftBlockWord, pairedLeftBlockLetterAt]

/-! ## Exact monitor runs -/

theorem profiledRawJointRightFirstThenBothMonitor_run_eq
    {Target : Type t} [Fintype Target]
    (targetState : Target → PairedProfiledTreeState A)
    (Allowed : Target → Prop)
    (source : ProfiledRawRightSlot A)
    (activation : ProfiledRawJointTargetRightBlockActivation A Target
      targetState Allowed source)
    (extension :
      ProfiledRawJointTargetRightFirstThenBothActivationExtension A activation)
    (env : Nat → In₂ × In₁) : ∀ n,
    (profiledRawJointRightFirstThenBothMonitor A Target targetState Allowed
      source.1.1).run
        (pairPlay
          (profiledRawJointTargetRightFirstThenBothReceiverStrategyOfExtension
            A activation extension)
          (pairedRightSenderStrategy activation.lambda) env) n =
      (profiledRawJointRightFirstThenBothScan A source.1.1
        (omegaPrefix (pairedRightBlockWord activation.lambda env) n), true) := by
  classical
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [BlockRecordMonitor.run, ih]
      have hphysical :=
        profiledRawJointTargetRightFirstThenBoth_pairPlay_physical A activation
          extension env n
      have hsafe := (extension.monitorLaws A env).targetSafe n
      simp only [profiledRawJointRightFirstThenBothMonitor]
      rw [hphysical]
      have htarget :
          ((pairPlay
            (profiledRawJointTargetRightFirstThenBothReceiverStrategyOfExtension
              A activation extension)
            (pairedRightSenderStrategy activation.lambda) env n).2.1
              ).firstThenBothTarget =
            extension.target (omegaPrefix env n) (env n) := by
        rw [profiledRawJointTargetRightFirstThenBoth_pairPlay_eq_letterAt A
          activation extension env n]
        rfl
      rw [htarget, decide_eq_true hsafe]
      rw [omegaPrefix_succ]
      unfold profiledRawJointRightFirstThenBothScan
      rw [List.foldl_append]
      rfl

theorem profiledRawJointLeftFirstThenBothMonitor_run_eq
    {Target : Type t} [Fintype Target]
    (targetState : Target → PairedProfiledTreeState A)
    (Allowed : Target → Prop)
    (source : ProfiledRawLeftSlot A)
    (activation : ProfiledRawJointTargetLeftBlockActivation A Target
      targetState Allowed source)
    (extension :
      ProfiledRawJointTargetLeftFirstThenBothActivationExtension A activation)
    (env : Nat → In₁ × In₂) : ∀ n,
    (profiledRawJointLeftFirstThenBothMonitor A Target targetState Allowed
      source.1.1).run
        (pairPlay
          (profiledRawJointTargetLeftFirstThenBothReceiverStrategyOfExtension A
            activation extension)
          (pairedLeftSenderStrategy activation.lambda) env) n =
      (profiledRawJointLeftFirstThenBothScan A source.1.1
        (omegaPrefix (pairedLeftBlockWord activation.lambda env) n), true) := by
  classical
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [BlockRecordMonitor.run, ih]
      have hphysical :=
        profiledRawJointTargetLeftFirstThenBoth_pairPlay_physical A activation
          extension env n
      have hsafe := (extension.monitorLaws A env).targetSafe n
      simp only [profiledRawJointLeftFirstThenBothMonitor]
      rw [hphysical]
      have htarget :
          ((pairPlay
            (profiledRawJointTargetLeftFirstThenBothReceiverStrategyOfExtension
              A activation extension)
            (pairedLeftSenderStrategy activation.lambda) env n).2.1
              ).firstThenBothTarget =
            extension.target (omegaPrefix env n) (env n) := by
        rw [profiledRawJointTargetLeftFirstThenBoth_pairPlay_eq_letterAt A
          activation extension env n]
        rfl
      rw [htarget, decide_eq_true hsafe]
      rw [omegaPrefix_succ]
      unfold profiledRawJointLeftFirstThenBothScan
      rw [List.foldl_append]
      rfl

/-! ## Scan/run correspondence -/

theorem profiledRawJointRightFirstThenBothScan_current_eq_runFrom
    (code : A.State × A.State)
    (letters : Nat → PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) : ∀ n,
    (profiledRawJointRightFirstThenBothScan A code
      (omegaPrefix letters n)).2.1 =
      A.runFrom code.1 (fun k ↦
        pairedRightRecordForRow (if k = 0 then .first else .both)
          (letters k)) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [omegaPrefix_succ]
      unfold profiledRawJointRightFirstThenBothScan
      rw [List.foldl_append]
      change A.step
          (profiledRawJointRightFirstThenBothScan A code
            (omegaPrefix letters n)).2.1
          (pairedRightRecordForRow
            (profiledRawJointFirstThenBothScanRow A
              (profiledRawJointRightFirstThenBothScan A code
                (omegaPrefix letters n))) (letters n)) = _
      rw [ih]
      by_cases hn : n = 0
      · subst n
        rfl
      · have hphase :
            (profiledRawJointRightFirstThenBothScan A code
              (omegaPrefix letters n)).1 = true := by
            cases n with
            | zero => contradiction
            | succ n =>
                rw [omegaPrefix_succ]
                unfold profiledRawJointRightFirstThenBothScan
                rw [List.foldl_append]
                rfl
        rw [DetParityAutomaton.runFrom]
        simp [profiledRawJointFirstThenBothScanRow, hphase, hn]

theorem profiledRawJointLeftFirstThenBothScan_current_eq_runFrom
    (code : A.State × A.State)
    (letters : Nat → PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) : ∀ n,
    (profiledRawJointLeftFirstThenBothScan A code
      (omegaPrefix letters n)).2.1 =
      A.runFrom code.1 (fun k ↦
        pairedLeftRecordForRow (if k = 0 then .first else .both)
          (letters k)) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [omegaPrefix_succ]
      unfold profiledRawJointLeftFirstThenBothScan
      rw [List.foldl_append]
      change A.step
          (profiledRawJointLeftFirstThenBothScan A code
            (omegaPrefix letters n)).2.1
          (pairedLeftRecordForRow
            (profiledRawJointFirstThenBothScanRow A
              (profiledRawJointLeftFirstThenBothScan A code
                (omegaPrefix letters n))) (letters n)) = _
      rw [ih]
      by_cases hn : n = 0
      · subst n
        rfl
      · have hphase :
            (profiledRawJointLeftFirstThenBothScan A code
              (omegaPrefix letters n)).1 = true := by
            cases n with
            | zero => contradiction
            | succ n =>
                rw [omegaPrefix_succ]
                unfold profiledRawJointLeftFirstThenBothScan
                rw [List.foldl_append]
                rfl
        rw [DetParityAutomaton.runFrom]
        simp [profiledRawJointFirstThenBothScanRow, hphase, hn]

/-! ## Realizability of the finite-safety lane -/

theorem profiledRawJointRightFirstThenBothMonitor_realizable
    {Target : Type t} [Fintype Target]
    (targetState : Target → PairedProfiledTreeState A)
    (Allowed : Target → Prop)
    (source : ProfiledRawRightSlot A)
    (activation : ProfiledRawJointTargetRightBlockActivation A Target
      targetState Allowed source)
    (extension :
      ProfiledRawJointTargetRightFirstThenBothActivationExtension A activation)
    (env : Nat → In₂ × In₁) :
    (profiledRawJointRightFirstThenBothMonitor A Target targetState Allowed
      source.1.1).WinsPlay
        (pairPlay
          (profiledRawJointTargetRightFirstThenBothReceiverStrategyOfExtension
            A activation extension)
          (pairedRightSenderStrategy activation.lambda) env) := by
  unfold BlockRecordMonitor.WinsPlay
  refine ⟨0, ⟨0, rfl⟩, ?_, ?_⟩
  · intro n
    refine ⟨n, le_rfl, ?_⟩
    dsimp only
    rw [profiledRawJointRightFirstThenBothMonitor_run_eq A targetState Allowed
      source activation extension env n]
    rfl
  · intro q _
    exact Nat.zero_le q

theorem profiledRawJointLeftFirstThenBothMonitor_realizable
    {Target : Type t} [Fintype Target]
    (targetState : Target → PairedProfiledTreeState A)
    (Allowed : Target → Prop)
    (source : ProfiledRawLeftSlot A)
    (activation : ProfiledRawJointTargetLeftBlockActivation A Target
      targetState Allowed source)
    (extension :
      ProfiledRawJointTargetLeftFirstThenBothActivationExtension A activation)
    (env : Nat → In₁ × In₂) :
    (profiledRawJointLeftFirstThenBothMonitor A Target targetState Allowed
      source.1.1).WinsPlay
        (pairPlay
          (profiledRawJointTargetLeftFirstThenBothReceiverStrategyOfExtension A
            activation extension)
          (pairedLeftSenderStrategy activation.lambda) env) := by
  unfold BlockRecordMonitor.WinsPlay
  refine ⟨0, ⟨0, rfl⟩, ?_, ?_⟩
  · intro n
    refine ⟨n, le_rfl, ?_⟩
    dsimp only
    rw [profiledRawJointLeftFirstThenBothMonitor_run_eq A targetState Allowed
      source activation extension env n]
    rfl
  · intro q _
    exact Nat.zero_le q

end

end DetParityAutomaton

end DistributedSynthesis
