/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridFullRestartFirstThenBothVirtualRootPriority

/-!
# Exact DPA states at row-aware mixed cuts

The mixed target already carries the exact minimum of the open part of a
strict block.  This module records its other operational role: its selected
`.first` state is the actual DPA state after the closing round.  Thus the
first-then-both scan supplies a complete local state/priority packet without
identifying its target with an old constant-row bank child.
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

private abbrev BankControl :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl A strategy hwin

private abbrev RetainedTag :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A strategy
    hwin

/-! ## Local state packets -/

/-- At a represented strict-right cut, the exact mixed target's selected
state is the physical DPA state immediately after the closing round. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRow_rightCut_firstThenBothTargetState
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (hnoBoth : ∀ n : Nat, (env n).graph ≠ .both)
    (k : Nat) (hgraph : (env (cuts.cuts k)).graph = .right)
    (root : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember)
    (hsender :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowRightBaseAt
          A strategy hwin initialTag env (cuts.cuts k)).1.1 =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightSenderAtPrefix
          A strategy hwin root family direction semanticMember hmember [])
    (hreceiver :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowRightBaseAt
          A strategy hwin initialTag env (cuts.cuts k)).1.2 =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightReceiverAtPrefix
          A strategy hwin root family direction semanticMember hmember false [])
    (hstate :
      A.run
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowWord
            A strategy hwin initialTag env) (cuts.cuts k) =
        (profiledRawRightSlotOfSemanticPair A semanticMember).1.1.1) :
    let activation :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightProfiledStateActivation
        A strategy hwin root family direction semanticMember hmember false
    let inputs : Nat → In₂ × In₁ := fun t ↦
      ((env (cuts.cuts k + t)).inputTwo,
        (env (cuts.cuts k + t)).inputOne)
    let target :=
      (profiledRawJointRightFirstThenBothProfiledStateExtension A activation
        ).target (omegaPrefix inputs (cuts.openLength k))
          (inputs (cuts.openLength k))
    ∃ slot : ProfiledRawLeftSlot A,
      target = .inr (.inr slot) ∧
        A.run
            (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowWord
              A strategy hwin initialTag env) (cuts.cuts (k + 1)) =
          pairedCodeStateForRow A .first slot.1.1 := by
  dsimp only
  let activation :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightProfiledStateActivation
      A strategy hwin root family direction semanticMember hmember false
  let lambda :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPhysicalLambda
      A strategy hwin root family direction semanticMember hmember false
  let inputs : Nat → In₂ × In₁ := fun t ↦
    ((env (cuts.cuts k + t)).inputTwo,
      (env (cuts.cuts k + t)).inputOne)
  let scan := profiledRawJointRightFirstThenBothScan A
    (profiledRawRightSlotOfSemanticPair A semanticMember).1.1
      (profiledRawJointRightBlockLetters lambda
        (omegaPrefix inputs (cuts.openLength k)))
  let row := profiledRawJointFirstThenBothScanRow A scan
  let target :=
    (profiledRawJointRightFirstThenBothProfiledStateExtension A activation
      ).target (omegaPrefix inputs (cuts.openLength k))
        (inputs (cuts.openLength k))
  let word :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowWord
      A strategy hwin initialTag env
  obtain ⟨slot, htarget⟩ :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRight_firstThenBothTarget_exists_leftSlot
      A strategy hwin root family direction semanticMember hmember
        (omegaPrefix inputs (cuts.openLength k))
        (inputs (cuts.openLength k))
  change target = .inr (.inr slot) at htarget
  refine ⟨slot, htarget, ?_⟩
  have hscan : scan.2.1 = A.run word
      (cuts.cuts k + cuts.openLength k) := by
    let block := profiledRawJointRightFirstThenBothRecords
      (profiledRawJointRightBlockLetters lambda
        (omegaPrefix inputs (cuts.openLength k)))
    have hslice :
        omegaPrefix (OmegaWord.drop word (cuts.cuts k)) block.length =
          block := by
      simpa [word, block, lambda, inputs] using
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRow_rightCut_firstThenBoth_slice
          A strategy hwin initialTag env cuts hnoBoth k hgraph root family
            direction semanticMember hmember hsender hreceiver)
    have hlength : block.length = cuts.openLength k := by
      dsimp only [block]
      rw [profiledRawJointRightBlockLetters_omegaPrefix,
        profiledRawJointRightFirstThenBothRecords_omegaPrefix]
      simp [omegaPrefix]
    have hscanBlock : scan.2 =
        blockEndAndMin A
          (profiledRawRightSlotOfSemanticPair A semanticMember).1.1.1 block := by
      simpa [scan, block, lambda, inputs] using
        (profiledRawJointRightFirstThenBothScan_eq_blockEndAndMin A
          (profiledRawRightSlotOfSemanticPair A semanticMember).1.1
          (profiledRawJointRightBlockLetters lambda
            (omegaPrefix inputs (cuts.openLength k))))
    have hdrop := A.runFrom_drop A.initial word (cuts.cuts k)
      (cuts.openLength k)
    change
      A.runFrom (A.run word (cuts.cuts k))
          (OmegaWord.drop word (cuts.cuts k)) (cuts.openLength k) =
        A.run word (cuts.cuts k + cuts.openLength k) at hdrop
    rw [hstate] at hdrop
    have hprefix :
        omegaPrefix (OmegaWord.drop word (cuts.cuts k))
            (cuts.openLength k) = block := by
      rw [← hlength]
      exact hslice
    calc
      scan.2.1 =
          (blockEndAndMin A
            (profiledRawRightSlotOfSemanticPair A semanticMember).1.1.1
              block).1 := congrArg Prod.fst hscanBlock
      _ = (blockEndAndMin A
          (profiledRawRightSlotOfSemanticPair A semanticMember).1.1.1
            (omegaPrefix (OmegaWord.drop word (cuts.cuts k))
              (cuts.openLength k))).1 := by rw [hprefix]
      _ = A.runFrom
          (profiledRawRightSlotOfSemanticPair A semanticMember).1.1.1
            (OmegaWord.drop word (cuts.cuts k)) (cuts.openLength k) := by
        exact blockEndAndMin_omegaPrefix_fst A _ _ _
      _ = A.run word (cuts.cuts k + cuts.openLength k) := hdrop
  have hclosing :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRow_rightCut_round_eq_linkedPhysicalWord
      A strategy hwin initialTag env cuts hnoBoth k hgraph root family
        direction semanticMember hmember hsender hreceiver
          (cuts.openLength k) (Nat.le_refl _)
  have hnextIndex : cuts.cuts (k + 1) =
      cuts.cuts k + cuts.openLength k + 1 := by
    rw [cuts.step_eq]
  have hrow : profiledRawJointFirstThenBothScanRow A scan =
      (if cuts.openLength k = 0 then .first else .both) := by
    by_cases hzero : cuts.openLength k = 0
    · dsimp only [scan]
      rw [hzero, profiledRawJointRightBlockLetters_omegaPrefix]
      rfl
    · have hphase : scan.1 = true := by
        obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hzero
        dsimp only [scan]
        rw [hn]
        rw [profiledRawJointRightBlockLetters_omegaPrefix, omegaPrefix_succ]
        unfold profiledRawJointRightFirstThenBothScan
        rw [List.foldl_append]
        rfl
      simp [profiledRawJointFirstThenBothScanRow, hphase, hzero]
  rw [hnextIndex, A.run_succ, ← hscan]
  simp [target, activation,
    profiledRawJointRightFirstThenBothProfiledStateExtension,
    profiledRawJointRightFirstThenBothProfiledCloseTarget,
    inputs] at htarget
  subst slot
  simp only [pairedCodeStateForRow]
  have hlambda : activation.lambda = lambda := by
    rfl
  rw [hlambda]
  apply congrArg (A.step scan.2.1)
  rw [hclosing, ← hrow]
  cases profiledRawJointFirstThenBothScanRow A scan <;>
    simp [
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPhysicalWord,
      pairedRightOmegaWord, pairedRightBlockLetterAt,
      pairedRightInformedForRow, lambda]

/-- Strict-left mirror of the exact mixed target-state packet. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRow_leftCut_firstThenBothTargetState
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (hnoBoth : ∀ n : Nat, (env n).graph ≠ .both)
    (k : Nat) (hgraph : (env (cuts.cuts k)).graph = .left)
    (root : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (hsender :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowLeftBaseAt
          A strategy hwin initialTag env (cuts.cuts k)).2.1 =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftSenderAtPrefix
          A strategy hwin root family direction semanticMember hmember [])
    (hreceiver :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowLeftBaseAt
          A strategy hwin initialTag env (cuts.cuts k)).2.2 =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftReceiverAtPrefix
          A strategy hwin root family direction semanticMember hmember false [])
    (hstate :
      A.run
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowWord
            A strategy hwin initialTag env) (cuts.cuts k) =
        (profiledRawLeftSlotOfSemanticPair A semanticMember).1.1.1) :
    let activation :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftProfiledStateActivation
        A strategy hwin root family direction semanticMember hmember false
    let inputs : Nat → In₁ × In₂ := fun t ↦
      ((env (cuts.cuts k + t)).inputOne,
        (env (cuts.cuts k + t)).inputTwo)
    let target :=
      (profiledRawJointLeftFirstThenBothProfiledStateExtension A activation
        ).target (omegaPrefix inputs (cuts.openLength k))
          (inputs (cuts.openLength k))
    ∃ slot : ProfiledRawRightSlot A,
      target = .inr (.inl slot) ∧
        A.run
            (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowWord
              A strategy hwin initialTag env) (cuts.cuts (k + 1)) =
          pairedCodeStateForRow A .first slot.1.1 := by
  dsimp only
  let activation :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftProfiledStateActivation
      A strategy hwin root family direction semanticMember hmember false
  let lambda :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPhysicalLambda
      A strategy hwin root family direction semanticMember hmember false
  let inputs : Nat → In₁ × In₂ := fun t ↦
    ((env (cuts.cuts k + t)).inputOne,
      (env (cuts.cuts k + t)).inputTwo)
  let scan := profiledRawJointLeftFirstThenBothScan A
    (profiledRawLeftSlotOfSemanticPair A semanticMember).1.1
      (profiledRawJointLeftBlockLetters lambda
        (omegaPrefix inputs (cuts.openLength k)))
  let row := profiledRawJointFirstThenBothScanRow A scan
  let target :=
    (profiledRawJointLeftFirstThenBothProfiledStateExtension A activation
      ).target (omegaPrefix inputs (cuts.openLength k))
        (inputs (cuts.openLength k))
  let word :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowWord
      A strategy hwin initialTag env
  obtain ⟨slot, htarget⟩ :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeft_firstThenBothTarget_exists_rightSlot
      A strategy hwin root family direction semanticMember hmember
        (omegaPrefix inputs (cuts.openLength k))
        (inputs (cuts.openLength k))
  change target = .inr (.inl slot) at htarget
  refine ⟨slot, htarget, ?_⟩
  have hscan : scan.2.1 = A.run word
      (cuts.cuts k + cuts.openLength k) := by
    let block := profiledRawJointLeftFirstThenBothRecords
      (profiledRawJointLeftBlockLetters lambda
        (omegaPrefix inputs (cuts.openLength k)))
    have hslice :
        omegaPrefix (OmegaWord.drop word (cuts.cuts k)) block.length =
          block := by
      simpa [word, block, lambda, inputs] using
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRow_leftCut_firstThenBoth_slice
          A strategy hwin initialTag env cuts hnoBoth k hgraph root family
            direction semanticMember hmember hsender hreceiver)
    have hlength : block.length = cuts.openLength k := by
      dsimp only [block]
      rw [profiledRawJointLeftBlockLetters_omegaPrefix,
        profiledRawJointLeftFirstThenBothRecords_omegaPrefix]
      simp [omegaPrefix]
    have hscanBlock : scan.2 =
        blockEndAndMin A
          (profiledRawLeftSlotOfSemanticPair A semanticMember).1.1.1 block := by
      simpa [scan, block, lambda, inputs] using
        (profiledRawJointLeftFirstThenBothScan_eq_blockEndAndMin A
          (profiledRawLeftSlotOfSemanticPair A semanticMember).1.1
          (profiledRawJointLeftBlockLetters lambda
            (omegaPrefix inputs (cuts.openLength k))))
    have hdrop := A.runFrom_drop A.initial word (cuts.cuts k)
      (cuts.openLength k)
    change
      A.runFrom (A.run word (cuts.cuts k))
          (OmegaWord.drop word (cuts.cuts k)) (cuts.openLength k) =
        A.run word (cuts.cuts k + cuts.openLength k) at hdrop
    rw [hstate] at hdrop
    have hprefix :
        omegaPrefix (OmegaWord.drop word (cuts.cuts k))
            (cuts.openLength k) = block := by
      rw [← hlength]
      exact hslice
    calc
      scan.2.1 =
          (blockEndAndMin A
            (profiledRawLeftSlotOfSemanticPair A semanticMember).1.1.1
              block).1 := congrArg Prod.fst hscanBlock
      _ = (blockEndAndMin A
          (profiledRawLeftSlotOfSemanticPair A semanticMember).1.1.1
            (omegaPrefix (OmegaWord.drop word (cuts.cuts k))
              (cuts.openLength k))).1 := by rw [hprefix]
      _ = A.runFrom
          (profiledRawLeftSlotOfSemanticPair A semanticMember).1.1.1
            (OmegaWord.drop word (cuts.cuts k)) (cuts.openLength k) := by
        exact blockEndAndMin_omegaPrefix_fst A _ _ _
      _ = A.run word (cuts.cuts k + cuts.openLength k) := hdrop
  have hclosing :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRow_leftCut_round_eq_linkedPhysicalWord
      A strategy hwin initialTag env cuts hnoBoth k hgraph root family
        direction semanticMember hmember hsender hreceiver
          (cuts.openLength k) (Nat.le_refl _)
  have hnextIndex : cuts.cuts (k + 1) =
      cuts.cuts k + cuts.openLength k + 1 := by
    rw [cuts.step_eq]
  have hrow : profiledRawJointFirstThenBothScanRow A scan =
      (if cuts.openLength k = 0 then .first else .both) := by
    by_cases hzero : cuts.openLength k = 0
    · dsimp only [scan]
      rw [hzero, profiledRawJointLeftBlockLetters_omegaPrefix]
      rfl
    · have hphase : scan.1 = true := by
        obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hzero
        dsimp only [scan]
        rw [hn]
        rw [profiledRawJointLeftBlockLetters_omegaPrefix, omegaPrefix_succ]
        unfold profiledRawJointLeftFirstThenBothScan
        rw [List.foldl_append]
        rfl
      simp [profiledRawJointFirstThenBothScanRow, hphase, hzero]
  rw [hnextIndex, A.run_succ, ← hscan]
  simp [target, activation,
    profiledRawJointLeftFirstThenBothProfiledStateExtension,
    profiledRawJointLeftFirstThenBothProfiledCloseTarget,
    inputs] at htarget
  subst slot
  simp only [pairedCodeStateForRow]
  have hlambda : activation.lambda = lambda := by
    rfl
  rw [hlambda]
  apply congrArg (A.step scan.2.1)
  rw [hclosing, ← hrow]
  cases profiledRawJointFirstThenBothScanRow A scan <;>
    simp [
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPhysicalWord,
      pairedLeftOmegaWord, pairedLeftBlockLetterAt,
      pairedLeftInformedForRow, lambda]

/-! ## Combined state/priority packets -/

/-- The strict-right mixed target simultaneously carries the physical block
minimum and the exact state after the closing round. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRow_rightCut_firstThenBothPacket
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (hnoBoth : ∀ n : Nat, (env n).graph ≠ .both)
    (k : Nat) (hgraph : (env (cuts.cuts k)).graph = .right)
    (root : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember)
    (hsender :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowRightBaseAt
          A strategy hwin initialTag env (cuts.cuts k)).1.1 =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightSenderAtPrefix
          A strategy hwin root family direction semanticMember hmember [])
    (hreceiver :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowRightBaseAt
          A strategy hwin initialTag env (cuts.cuts k)).1.2 =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightReceiverAtPrefix
          A strategy hwin root family direction semanticMember hmember false [])
    (hstate :
      A.run
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowWord
            A strategy hwin initialTag env) (cuts.cuts k) =
        (profiledRawRightSlotOfSemanticPair A semanticMember).1.1.1) :
    let activation :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightProfiledStateActivation
        A strategy hwin root family direction semanticMember hmember false
    let inputs : Nat → In₂ × In₁ := fun t ↦
      ((env (cuts.cuts k + t)).inputTwo,
        (env (cuts.cuts k + t)).inputOne)
    let target :=
      (profiledRawJointRightFirstThenBothProfiledStateExtension A activation
        ).target (omegaPrefix inputs (cuts.openLength k))
          (inputs (cuts.openLength k))
    ∃ slot : ProfiledRawLeftSlot A,
      target = .inr (.inr slot) ∧
        cutBlockMin
            (fun n ↦
              A.priority
                (A.run
                  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowWord
                    A strategy hwin initialTag env) n)) cuts.cuts k =
          profiledRawJointThreadRootPriority A (.inr slot) ∧
        A.run
            (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowWord
              A strategy hwin initialTag env) (cuts.cuts (k + 1)) =
          pairedCodeStateForRow A .first slot.1.1 := by
  dsimp only
  let activation :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightProfiledStateActivation
      A strategy hwin root family direction semanticMember hmember false
  let inputs : Nat → In₂ × In₁ := fun t ↦
    ((env (cuts.cuts k + t)).inputTwo,
      (env (cuts.cuts k + t)).inputOne)
  let target :=
    (profiledRawJointRightFirstThenBothProfiledStateExtension A activation
      ).target (omegaPrefix inputs (cuts.openLength k))
        (inputs (cuts.openLength k))
  obtain ⟨slot, htarget, hnext⟩ :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRow_rightCut_firstThenBothTargetState
      A strategy hwin initialTag env cuts hnoBoth k hgraph root family
        direction semanticMember hmember hsender hreceiver hstate
  have hpriority :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRow_rightCut_cutBlockMin_eq_firstThenBothTargetPriority
      A strategy hwin initialTag env cuts hnoBoth k hgraph root family
        direction semanticMember hmember hsender hreceiver hstate
  change
    cutBlockMin
        (fun n ↦
          A.priority
            (A.run
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowWord
                A strategy hwin initialTag env) n)) cuts.cuts k =
      pairedProfiledEntryPriority A target at hpriority
  change target = .inr (.inr slot) at htarget
  refine ⟨slot, htarget, ?_, hnext⟩
  rw [hpriority, htarget]
  rfl

/-- Strict-left combined state/priority packet. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRow_leftCut_firstThenBothPacket
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (hnoBoth : ∀ n : Nat, (env n).graph ≠ .both)
    (k : Nat) (hgraph : (env (cuts.cuts k)).graph = .left)
    (root : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (hsender :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowLeftBaseAt
          A strategy hwin initialTag env (cuts.cuts k)).2.1 =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftSenderAtPrefix
          A strategy hwin root family direction semanticMember hmember [])
    (hreceiver :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowLeftBaseAt
          A strategy hwin initialTag env (cuts.cuts k)).2.2 =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftReceiverAtPrefix
          A strategy hwin root family direction semanticMember hmember false [])
    (hstate :
      A.run
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowWord
            A strategy hwin initialTag env) (cuts.cuts k) =
        (profiledRawLeftSlotOfSemanticPair A semanticMember).1.1.1) :
    let activation :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftProfiledStateActivation
        A strategy hwin root family direction semanticMember hmember false
    let inputs : Nat → In₁ × In₂ := fun t ↦
      ((env (cuts.cuts k + t)).inputOne,
        (env (cuts.cuts k + t)).inputTwo)
    let target :=
      (profiledRawJointLeftFirstThenBothProfiledStateExtension A activation
        ).target (omegaPrefix inputs (cuts.openLength k))
          (inputs (cuts.openLength k))
    ∃ slot : ProfiledRawRightSlot A,
      target = .inr (.inl slot) ∧
        cutBlockMin
            (fun n ↦
              A.priority
                (A.run
                  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowWord
                    A strategy hwin initialTag env) n)) cuts.cuts k =
          profiledRawJointThreadRootPriority A (.inl slot) ∧
        A.run
            (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowWord
              A strategy hwin initialTag env) (cuts.cuts (k + 1)) =
          pairedCodeStateForRow A .first slot.1.1 := by
  dsimp only
  let activation :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftProfiledStateActivation
      A strategy hwin root family direction semanticMember hmember false
  let inputs : Nat → In₁ × In₂ := fun t ↦
    ((env (cuts.cuts k + t)).inputOne,
      (env (cuts.cuts k + t)).inputTwo)
  let target :=
    (profiledRawJointLeftFirstThenBothProfiledStateExtension A activation
      ).target (omegaPrefix inputs (cuts.openLength k))
        (inputs (cuts.openLength k))
  obtain ⟨slot, htarget, hnext⟩ :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRow_leftCut_firstThenBothTargetState
      A strategy hwin initialTag env cuts hnoBoth k hgraph root family
        direction semanticMember hmember hsender hreceiver hstate
  have hpriority :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRow_leftCut_cutBlockMin_eq_firstThenBothTargetPriority
      A strategy hwin initialTag env cuts hnoBoth k hgraph root family
        direction semanticMember hmember hsender hreceiver hstate
  change
    cutBlockMin
        (fun n ↦
          A.priority
            (A.run
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowWord
                A strategy hwin initialTag env) n)) cuts.cuts k =
      pairedProfiledEntryPriority A target at hpriority
  change target = .inr (.inl slot) at htarget
  refine ⟨slot, htarget, ?_, hnext⟩
  rw [hpriority, htarget]
  rfl

end

end DetParityAutomaton

end DistributedSynthesis
