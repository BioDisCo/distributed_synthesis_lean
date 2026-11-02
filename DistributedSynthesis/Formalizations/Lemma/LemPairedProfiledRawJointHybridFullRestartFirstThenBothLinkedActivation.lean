/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridFullRestartFirstThenBothProfiledTarget
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankLinkedDeferredFixedTailBridge

/-!
# First-then-both activation of a retained linked table

The table emitted by the executable bank is already finite, but its physical
lambda is a rationalized projection rather than the semantic sibling lambda.
This module packages that exact projected lambda as an activation.  It is the
source-level bridge needed to apply the mixed finite-safety controller to the
literal table occurring in the global run.
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

/-! ## Initial overlap profiles of the exact linked projection -/

/-- Rationalization preserves the initial right overlap profile. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPhysicalLambda_initialProfile
    (state : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember)
    (anchor : Bool) :
    let activation :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankRightActivations
        A strategy hwin family direction semanticMember hmember anchor
    rightInitialFirstProfile
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPhysicalLambda
          A strategy hwin state family direction semanticMember hmember anchor) =
      (profiledRawRightSlotOfSemanticPair A semanticMember).2 := by
  dsimp only
  let activation :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRightActivations
      A strategy hwin family direction semanticMember hmember anchor
  rw [← activation.initial_profile]
  funext input
  have hpair :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOf_initial_first_pair
      A strategy hwin state family direction semanticMember hmember anchor input
  simpa [rightInitialFirstProfile,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPhysicalLambda,
    activation,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRightActivations]
    using congrArg (fun pair ↦ pair.1.physical.informedFirst) hpair

/-- Left initial-overlap mirror. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPhysicalLambda_initialProfile
    (state : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (anchor : Bool) :
    let activation :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftActivations
        A strategy hwin family direction semanticMember hmember anchor
    leftInitialFirstProfile
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPhysicalLambda
          A strategy hwin state family direction semanticMember hmember anchor) =
      (profiledRawLeftSlotOfSemanticPair A semanticMember).2 := by
  dsimp only
  let activation :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftActivations
      A strategy hwin family direction semanticMember hmember anchor
  rw [← activation.initial_profile]
  funext input
  have hpair :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOf_initial_first_pair
      A strategy hwin state family direction semanticMember hmember anchor input
  simpa [leftInitialFirstProfile,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPhysicalLambda,
    activation,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftActivations]
    using congrArg (fun pair ↦ pair.1.physical.informedFirst) hpair

/-! ## Activations of the projected linked lambdas -/

/-- The exact physical lambda of a retained right linked table, exposed over
the full finite profiled-state target alphabet. -/
def profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightProfiledStateActivation
    (state : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember)
    (anchor : Bool) :
    let semanticActivation :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankRightActivations
        A strategy hwin family direction semanticMember hmember anchor
    ProfiledRawJointTargetRightBlockActivation A (PairedProfiledTreeState A)
      id (fun _ ↦ True)
        (profiledRawRightSlotOfSemanticPair A semanticMember) := by
  dsimp only
  let semanticActivation :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRightActivations
      A strategy hwin family direction semanticMember hmember anchor
  let lambda :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPhysicalLambda
      A strategy hwin state family direction semanticMember hmember anchor
  exact {
    lambda := lambda
    initial_profile := by
      exact
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPhysicalLambda_initialProfile
          A strategy hwin state family direction semanticMember hmember anchor
    forever := by
      simpa [semanticActivation] using
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPhysicalLambda_forever
          A strategy hwin state family direction semanticMember hmember anchor)
    target := fun row past input ↦
      .inr (.inr
        (profiledRawRightChildSlot A
          (profiledRawRightSlotOfSemanticPair A semanticMember) lambda row
            past input))
    target_allowed := by simp
    target_state := by intro row past input; rfl
  }

/-- Left projected linked activation. -/
def profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftProfiledStateActivation
    (state : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (anchor : Bool) :
    let semanticActivation :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftActivations
        A strategy hwin family direction semanticMember hmember anchor
    ProfiledRawJointTargetLeftBlockActivation A (PairedProfiledTreeState A)
      id (fun _ ↦ True)
        (profiledRawLeftSlotOfSemanticPair A semanticMember) := by
  dsimp only
  let semanticActivation :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftActivations
      A strategy hwin family direction semanticMember hmember anchor
  let lambda :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPhysicalLambda
      A strategy hwin state family direction semanticMember hmember anchor
  exact {
    lambda := lambda
    initial_profile := by
      exact
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPhysicalLambda_initialProfile
          A strategy hwin state family direction semanticMember hmember anchor
    forever := by
      simpa [semanticActivation] using
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPhysicalLambda_forever
          A strategy hwin state family direction semanticMember hmember anchor)
    target := fun row past input ↦
      .inr (.inl
        (profiledRawLeftChildSlot A
          (profiledRawLeftSlotOfSemanticPair A semanticMember) lambda row past
            input))
    target_allowed := by simp
    target_state := by intro row past input; rfl
  }

/-! ## Finite mixed controllers for the exact retained tables -/

/-- The literal physical lambda of every retained linked right occurrence
has an unconditional finite first-then-both safety controller. -/
theorem
    exists_profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightFirstThenBothController
    (state : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember)
    (anchor : Bool) :
    let source := profiledRawRightSlotOfSemanticPair A semanticMember
    ∃ controller :
        TransitionRationalTree.{u, max u v x y s, max u v x y s} In₁
          (NarrowedBlockLabel In₂ In₁
            (ProfiledRawJointRightFirstThenBothReceiverOutput
              (Out₁ := Out₁) (Out₂ := Out₂) (PairedProfiledTreeState A))
            Out₁
            (profiledRawJointTargetRightFirstThenBothCombinedMonitor A
              (PairedProfiledTreeState A) id (fun _ ↦ True) source).State),
      NarrowedAllThreadsWin
        (profiledRawJointTargetRightFirstThenBothCombinedMonitor A
          (PairedProfiledTreeState A) id (fun _ ↦ True) source)
        controller.labeledTree := by
  dsimp only
  exact exists_profiledRawJointRightFirstThenBothProfiledStateController A
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightProfiledStateActivation
      A strategy hwin state family direction semanticMember hmember anchor)

/-- Left retained-table mirror. -/
theorem
    exists_profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftFirstThenBothController
    (state : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (anchor : Bool) :
    let source := profiledRawLeftSlotOfSemanticPair A semanticMember
    ∃ controller :
        TransitionRationalTree.{v, max u v x y s, max u v y s} In₂
          (NarrowedBlockLabel In₁ In₂
            (ProfiledRawJointLeftFirstThenBothReceiverOutput
              (Out₁ := Out₁) (Out₂ := Out₂) (PairedProfiledTreeState A))
            Out₂
            (profiledRawJointTargetLeftFirstThenBothCombinedMonitor A
              (PairedProfiledTreeState A) id (fun _ ↦ True) source).State),
      NarrowedAllThreadsWin
        (profiledRawJointTargetLeftFirstThenBothCombinedMonitor A
          (PairedProfiledTreeState A) id (fun _ ↦ True) source)
        controller.labeledTree := by
  dsimp only
  exact exists_profiledRawJointLeftFirstThenBothProfiledStateController A
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftProfiledStateActivation
      A strategy hwin state family direction semanticMember hmember anchor)

end

end DetParityAutomaton

end DistributedSynthesis
