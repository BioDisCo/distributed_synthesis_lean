/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridFullRestartFirstThenBothRowCutPriority

/-!
# Virtual thread roots carried by row-aware mixed cuts

The exact first-then-both target is a finite profiled paired state.  This
module records its outer one-sided shape and therefore re-expresses the
literal cut minimum as a `ProfiledRawJointThreadRoot` priority.  The root is
the mixed finite certificate; no claim is made here that it is the constant-
row semantic child installed by the bank.
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

/-! ## Shape of the exact mixed target -/

theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRight_firstThenBothTarget_exists_leftSlot
    (state : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember)
    (past : List (In₂ × In₁)) (input : In₂ × In₁) :
    let activation :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightProfiledStateActivation
        A strategy hwin state family direction semanticMember hmember false
    let target :=
      (profiledRawJointRightFirstThenBothProfiledStateExtension A activation
        ).target past input
    ∃ slot : ProfiledRawLeftSlot A, target = .inr (.inr slot) := by
  dsimp only
  simp [profiledRawJointRightFirstThenBothProfiledStateExtension,
    profiledRawJointRightFirstThenBothProfiledCloseTarget]

theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeft_firstThenBothTarget_exists_rightSlot
    (state : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (past : List (In₁ × In₂)) (input : In₁ × In₂) :
    let activation :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftProfiledStateActivation
        A strategy hwin state family direction semanticMember hmember false
    let target :=
      (profiledRawJointLeftFirstThenBothProfiledStateExtension A activation
        ).target past input
    ∃ slot : ProfiledRawRightSlot A, target = .inr (.inl slot) := by
  dsimp only
  simp [profiledRawJointLeftFirstThenBothProfiledStateExtension,
    profiledRawJointLeftFirstThenBothProfiledCloseTarget]

/-! ## Operational cut minima as virtual root priorities -/

theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRow_rightCut_exists_virtualRootPriority
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
    ∃ slot : ProfiledRawLeftSlot A,
      cutBlockMin
          (fun n ↦
            A.priority
              (A.run
                (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowWord
                  A strategy hwin initialTag env) n)) cuts.cuts k =
        profiledRawJointThreadRootPriority A (.inr slot) := by
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
  have hpriority :
      cutBlockMin
          (fun n ↦
            A.priority
              (A.run
                (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowWord
                  A strategy hwin initialTag env) n)) cuts.cuts k =
        pairedProfiledEntryPriority A target := by
    simpa [activation, inputs, target] using
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRow_rightCut_cutBlockMin_eq_firstThenBothTargetPriority
        A strategy hwin initialTag env cuts hnoBoth k hgraph root family
          direction semanticMember hmember hsender hreceiver hstate)
  obtain ⟨slot, htarget⟩ :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRight_firstThenBothTarget_exists_leftSlot
      A strategy hwin root family direction semanticMember hmember
        (omegaPrefix inputs (cuts.openLength k))
        (inputs (cuts.openLength k))
  change target = .inr (.inr slot) at htarget
  refine ⟨slot, ?_⟩
  rw [hpriority, htarget]
  rfl

/-- Strict-left mirror. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRow_leftCut_exists_virtualRootPriority
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
    ∃ slot : ProfiledRawRightSlot A,
      cutBlockMin
          (fun n ↦
            A.priority
              (A.run
                (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowWord
                  A strategy hwin initialTag env) n)) cuts.cuts k =
        profiledRawJointThreadRootPriority A (.inl slot) := by
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
  have hpriority :
      cutBlockMin
          (fun n ↦
            A.priority
              (A.run
                (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowWord
                  A strategy hwin initialTag env) n)) cuts.cuts k =
        pairedProfiledEntryPriority A target := by
    simpa [activation, inputs, target] using
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRow_leftCut_cutBlockMin_eq_firstThenBothTargetPriority
        A strategy hwin initialTag env cuts hnoBoth k hgraph root family
          direction semanticMember hmember hsender hreceiver hstate)
  obtain ⟨slot, htarget⟩ :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeft_firstThenBothTarget_exists_rightSlot
      A strategy hwin root family direction semanticMember hmember
        (omegaPrefix inputs (cuts.openLength k))
        (inputs (cuts.openLength k))
  change target = .inr (.inl slot) at htarget
  refine ⟨slot, ?_⟩
  rw [hpriority, htarget]
  rfl

end

end DetParityAutomaton

end DistributedSynthesis
