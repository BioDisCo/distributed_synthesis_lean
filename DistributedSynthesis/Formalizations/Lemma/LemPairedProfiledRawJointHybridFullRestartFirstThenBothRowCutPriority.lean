/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridFullRestartFirstThenBothLinkedActivation
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowCutOutput
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenAutomaticRecutEpochCoupling

/-!
# Exact first-then-both priorities at row-aware restart cuts

This module identifies the finite mixed target carried by the new controller
with the literal DPA minimum of an operational strict block.  The closing
letter is excluded from the minimum and determines the next profiled target,
exactly matching the convention of `cutBlockMin`.
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

/-! ## Exact literal slices -/

/-- The open part of a strict-right operational block is exactly the mixed
record prefix computed by the linked physical lambda. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRow_rightCut_firstThenBoth_slice
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
          A strategy hwin root family direction semanticMember hmember false []) :
    let lambda :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPhysicalLambda
        A strategy hwin root family direction semanticMember hmember false
    let inputs : Nat → In₂ × In₁ := fun t ↦
      ((env (cuts.cuts k + t)).inputTwo,
        (env (cuts.cuts k + t)).inputOne)
    let block :=
      profiledRawJointRightFirstThenBothRecords
        (profiledRawJointRightBlockLetters lambda
          (omegaPrefix inputs (cuts.openLength k)))
    omegaPrefix
        (OmegaWord.drop
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowWord
            A strategy hwin initialTag env) (cuts.cuts k)) block.length =
      block := by
  dsimp only
  let lambda :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPhysicalLambda
      A strategy hwin root family direction semanticMember hmember false
  let inputs : Nat → In₂ × In₁ := fun t ↦
    ((env (cuts.cuts k + t)).inputTwo,
      (env (cuts.cuts k + t)).inputOne)
  rw [profiledRawJointRightBlockLetters_omegaPrefix,
    profiledRawJointRightFirstThenBothRecords_omegaPrefix]
  apply List.ext_get
  · simp [omegaPrefix]
  · intro j hjLeft hjRight
    rw [List.get_eq_getElem, List.get_eq_getElem]
    simp only [omegaPrefix, List.getElem_ofFn, OmegaWord.drop_apply]
    have hj : j < cuts.openLength k := by
      simpa [omegaPrefix] using hjRight
    rw [
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRow_rightCut_round_eq_linkedPhysicalWord
        A strategy hwin initialTag env cuts hnoBoth k hgraph root family
          direction semanticMember hmember hsender hreceiver j
            (Nat.le_of_lt hj)]
    by_cases hzero : j = 0 <;>
      simp [hzero,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPhysicalWord,
        pairedRightOmegaWord, pairedRightBlockWord, pairedRightRecordForRow]

/-- Strict-left mirror of the literal mixed slice. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRow_leftCut_firstThenBoth_slice
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
          A strategy hwin root family direction semanticMember hmember false []) :
    let lambda :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPhysicalLambda
        A strategy hwin root family direction semanticMember hmember false
    let inputs : Nat → In₁ × In₂ := fun t ↦
      ((env (cuts.cuts k + t)).inputOne,
        (env (cuts.cuts k + t)).inputTwo)
    let block :=
      profiledRawJointLeftFirstThenBothRecords
        (profiledRawJointLeftBlockLetters lambda
          (omegaPrefix inputs (cuts.openLength k)))
    omegaPrefix
        (OmegaWord.drop
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowWord
            A strategy hwin initialTag env) (cuts.cuts k)) block.length =
      block := by
  dsimp only
  let lambda :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPhysicalLambda
      A strategy hwin root family direction semanticMember hmember false
  let inputs : Nat → In₁ × In₂ := fun t ↦
    ((env (cuts.cuts k + t)).inputOne,
      (env (cuts.cuts k + t)).inputTwo)
  rw [profiledRawJointLeftBlockLetters_omegaPrefix,
    profiledRawJointLeftFirstThenBothRecords_omegaPrefix]
  apply List.ext_get
  · simp [omegaPrefix]
  · intro j hjLeft hjRight
    rw [List.get_eq_getElem, List.get_eq_getElem]
    simp only [omegaPrefix, List.getElem_ofFn, OmegaWord.drop_apply]
    have hj : j < cuts.openLength k := by
      simpa [omegaPrefix] using hjRight
    rw [
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRow_leftCut_round_eq_linkedPhysicalWord
        A strategy hwin initialTag env cuts hnoBoth k hgraph root family
          direction semanticMember hmember hsender hreceiver j
            (Nat.le_of_lt hj)]
    by_cases hzero : j = 0 <;>
      simp [hzero,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPhysicalWord,
        pairedLeftOmegaWord, pairedLeftBlockWord, pairedLeftBlockLetterAt,
        pairedLeftRecordForRow]

/-! ## Operational cut minima carried by the exact mixed targets -/

/-- At a represented strict-right cut, the exact mixed target emitted on the
closing input carries precisely the original DPA `cutBlockMin`. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRow_rightCut_cutBlockMin_eq_firstThenBothTargetPriority
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
    cutBlockMin
        (fun n ↦
          A.priority
            (A.run
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowWord
                A strategy hwin initialTag env) n)) cuts.cuts k =
      pairedProfiledEntryPriority A target := by
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
  let block :=
    profiledRawJointRightFirstThenBothRecords
      (profiledRawJointRightBlockLetters lambda
        (omegaPrefix inputs (cuts.openLength k)))
  let word :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowWord
      A strategy hwin initialTag env
  have hslice :
      omegaPrefix (OmegaWord.drop word (cuts.cuts k)) block.length =
        block := by
    simpa [word, block, lambda, inputs] using
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRow_rightCut_firstThenBoth_slice
        A strategy hwin initialTag env cuts hnoBoth k hgraph root family
          direction semanticMember hmember hsender hreceiver)
  have hlength :
      block.length = cuts.cuts (k + 1) - cuts.cuts k - 1 := by
    dsimp only [block]
    rw [profiledRawJointRightBlockLetters_omegaPrefix,
      profiledRawJointRightFirstThenBothRecords_omegaPrefix]
    simp only [omegaPrefix, List.length_ofFn]
    rw [cuts.step_eq]
    omega
  have hphysical :
      cutBlockMin (fun n ↦ A.priority (A.run word n)) cuts.cuts k =
        A.priority
          (blockMinState A
            (profiledRawRightSlotOfSemanticPair A semanticMember).1.1.1
              block) := by
    simpa [word] using
      (cutBlockMin_eq_priority_blockMinState_of_slice_alignment A word 0
        cuts.cuts k
          (profiledRawRightSlotOfSemanticPair A semanticMember).1.1.1 block
            (by simpa [word] using hstate) hlength
              (by simpa only [Nat.zero_add] using hslice))
  have htarget :=
    profiledRawJointRightFirstThenBothProfiledStateExtension_priority_eq_blockMin
      A activation (omegaPrefix inputs (cuts.openLength k))
        (inputs (cuts.openLength k))
  calc
    cutBlockMin (fun n ↦ A.priority (A.run word n)) cuts.cuts k =
        A.priority
          (blockMinState A
            (profiledRawRightSlotOfSemanticPair A semanticMember).1.1.1
              block) := hphysical
    _ = pairedProfiledEntryPriority A
          ((profiledRawJointRightFirstThenBothProfiledStateExtension A
            activation).target (omegaPrefix inputs (cuts.openLength k))
              (inputs (cuts.openLength k))) := by
      simpa [activation, block, lambda] using htarget.symm

/-- Strict-left mirror of the exact mixed target-priority handoff. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRow_leftCut_cutBlockMin_eq_firstThenBothTargetPriority
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
    cutBlockMin
        (fun n ↦
          A.priority
            (A.run
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowWord
                A strategy hwin initialTag env) n)) cuts.cuts k =
      pairedProfiledEntryPriority A target := by
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
  let block :=
    profiledRawJointLeftFirstThenBothRecords
      (profiledRawJointLeftBlockLetters lambda
        (omegaPrefix inputs (cuts.openLength k)))
  let word :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowWord
      A strategy hwin initialTag env
  have hslice :
      omegaPrefix (OmegaWord.drop word (cuts.cuts k)) block.length =
        block := by
    simpa [word, block, lambda, inputs] using
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRow_leftCut_firstThenBoth_slice
        A strategy hwin initialTag env cuts hnoBoth k hgraph root family
          direction semanticMember hmember hsender hreceiver)
  have hlength :
      block.length = cuts.cuts (k + 1) - cuts.cuts k - 1 := by
    dsimp only [block]
    rw [profiledRawJointLeftBlockLetters_omegaPrefix,
      profiledRawJointLeftFirstThenBothRecords_omegaPrefix]
    simp only [omegaPrefix, List.length_ofFn]
    rw [cuts.step_eq]
    omega
  have hphysical :
      cutBlockMin (fun n ↦ A.priority (A.run word n)) cuts.cuts k =
        A.priority
          (blockMinState A
            (profiledRawLeftSlotOfSemanticPair A semanticMember).1.1.1
              block) := by
    simpa [word] using
      (cutBlockMin_eq_priority_blockMinState_of_slice_alignment A word 0
        cuts.cuts k
          (profiledRawLeftSlotOfSemanticPair A semanticMember).1.1.1 block
            (by simpa [word] using hstate) hlength
              (by simpa only [Nat.zero_add] using hslice))
  have htarget :=
    profiledRawJointLeftFirstThenBothProfiledStateExtension_priority_eq_blockMin
      A activation (omegaPrefix inputs (cuts.openLength k))
        (inputs (cuts.openLength k))
  calc
    cutBlockMin (fun n ↦ A.priority (A.run word n)) cuts.cuts k =
        A.priority
          (blockMinState A
            (profiledRawLeftSlotOfSemanticPair A semanticMember).1.1.1
              block) := hphysical
    _ = pairedProfiledEntryPriority A
          ((profiledRawJointLeftFirstThenBothProfiledStateExtension A
            activation).target (omegaPrefix inputs (cuts.openLength k))
              (inputs (cuts.openLength k))) := by
      simpa [activation, block, lambda] using htarget.symm

end

end DetParityAutomaton

end DistributedSynthesis
