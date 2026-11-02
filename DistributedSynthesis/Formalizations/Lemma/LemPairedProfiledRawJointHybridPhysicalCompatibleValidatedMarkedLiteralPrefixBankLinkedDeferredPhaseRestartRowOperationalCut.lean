/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowReceive
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankOperationalSemanticCutPath
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankOperationalPhaseBits

/-!
# Operational cuts of the phase-restarted linked controller

This module exposes the authoritative marked-bank coordinate of the repaired
phase-restart semantic trace.  The first layer below is deliberately
round-local: it proves the exact strict receiver child and simultaneous child
equations without mentioning a graph side in either executable transition.
The later block layer groups those rounds at the operational-close clock.
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

private abbrev LinkedOne :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedOneControl
    A strategy hwin

private abbrev LinkedTwo :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedTwoControl
    A strategy hwin

private abbrev Payload :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPayload A
    strategy hwin

private abbrev OneControl :=
  FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
    (LinkedOne A strategy hwin) (Payload A strategy hwin) PUnit.{1}

private abbrev TwoControl :=
  FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
    (LinkedTwo A strategy hwin) (Payload A strategy hwin) PUnit.{1}

/-! ## The repaired authority coordinate -/

/-- Process one's receive-normalized marked-bank parent before round `n`. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowParentOneAt
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    BankControl A strategy hwin :=
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin initialTag
  let pair :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSemanticPairAt
      A strategy hwin initialTag env n
  profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOne
    A strategy hwin
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
        A strategy hwin fallback.1 pair.1)
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
        A strategy hwin fallback.2 pair.2)

/-- Process-two mirror of the repaired authority coordinate. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowParentTwoAt
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    BankControl A strategy hwin :=
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin initialTag
  let pair :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSemanticPairAt
      A strategy hwin initialTag env n
  profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentTwo
    A strategy hwin
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
        A strategy hwin fallback.1 pair.1)
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
        A strategy hwin fallback.2 pair.2)

theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowParentsAt_eq
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowParentOneAt
        A strategy hwin initialTag env n =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowParentTwoAt
        A strategy hwin initialTag env n := by
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin initialTag
  let pair :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSemanticPairAt
      A strategy hwin initialTag env n
  have hinvariant :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSemanticPairAt_invariant
      A strategy hwin initialTag env n
  exact
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentsAgree_of_selectedAuthorityCompatible
      A strategy hwin fallback pair.1 pair.2 hinvariant.2

/-! ## Round-local authority equations -/

private theorem phaseRestartRowParentOne_strictRight
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (one : OneControl A strategy hwin) (inputOne : In₁)
    (two : TwoControl A strategy hwin) (inputTwo : In₂)
    (hpending :
      FiniteAcknowledgedDelayedCarrier.DeferredPairIsPending one two) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOne
        A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
          A strategy hwin fallback.1
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvOne
            A strategy hwin one inputOne).1)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
          A strategy hwin fallback.2
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowOpenRecvTwo
            A strategy hwin fallback two inputTwo one inputOne).1) =
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowReceivedTwo
        A strategy hwin fallback two inputTwo one inputOne).child A strategy
          hwin := by
  cases one with
  | inr recurrent => exact False.elim hpending.1
  | inl onePending =>
      cases two with
      | inr recurrent => exact False.elim hpending.2
      | inl twoPending =>
          simp only [
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOne,
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedOne_noRecv_lastRecv,
            Bool.false_eq_true, ↓reduceIte]
          rfl

private theorem phaseRestartRowParentOne_strictLeft
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (one : OneControl A strategy hwin) (inputOne : In₁)
    (two : TwoControl A strategy hwin) (inputTwo : In₂)
    (hpending :
      FiniteAcknowledgedDelayedCarrier.DeferredPairIsPending one two) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOne
        A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
          A strategy hwin fallback.1
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowOpenRecvOne
            A strategy hwin fallback one inputOne two inputTwo).1)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
          A strategy hwin fallback.2
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvTwo
            A strategy hwin two inputTwo).1) =
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowReceivedOne
        A strategy hwin fallback one inputOne two inputTwo).child A strategy
          hwin := by
  cases one with
  | inr recurrent => exact False.elim hpending.1
  | inl onePending =>
      cases two with
      | inr recurrent => exact False.elim hpending.2
      | inl twoPending =>
          simp only [
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOne,
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSelectedOne_openRecv_lastRecv,
            ↓reduceIte]
          rfl

private theorem phaseRestartRowParentOne_both
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (one : OneControl A strategy hwin) (inputOne : In₁)
    (two : TwoControl A strategy hwin) (inputTwo : In₂)
    (hparents :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentsAgree
        A strategy hwin fallback one two) :
    let next :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowClose
        A strategy hwin fallback one inputOne two inputTwo
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOne
        A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
          A strategy hwin fallback.1 next.1)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
          A strategy hwin fallback.2 next.2) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
        hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOne
          A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
            A strategy hwin fallback.1 one)
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
            A strategy hwin fallback.2 two))
        (.simultaneous (inputOne, inputTwo)) := by
  let freshOne :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowFreshOne
      A strategy hwin fallback one inputOne two inputTwo
  let freshTwo :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowFreshTwo
      A strategy hwin fallback two inputTwo one inputOne
  have hselectedTwo :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
        A strategy hwin fallback.2
          (.inl (true, freshTwo.1, freshTwo.2) : TwoControl A strategy hwin)
        ).child A strategy hwin =
      (freshTwo.2.tag A strategy hwin true).1 :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo_closed_child
      A strategy hwin fallback.2 freshTwo.1 freshTwo.2
  have hselectedOneFlag :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
        A strategy hwin fallback.1
          (.inl (true, freshOne.1, freshOne.2) : OneControl A strategy hwin)
        ).2.1 = false := rfl
  have hfreshTwo :
      (freshTwo.2.tag A strategy hwin true).1 =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
          strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentTwo
            A strategy hwin
            (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
              A strategy hwin fallback.1 one)
            (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
              A strategy hwin fallback.2 two))
          (.simultaneous (inputOne, inputTwo)) := by
    exact
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowFreshTwo_closed_child
        A strategy hwin fallback two inputTwo one inputOne
  have hparentEq :
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentTwo
          A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
            A strategy hwin fallback.1 one)
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
            A strategy hwin fallback.2 two) =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOne
          A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
            A strategy hwin fallback.1 one)
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
            A strategy hwin fallback.2 two) := hparents.symm
  dsimp only [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowClose,
    FiniteAcknowledgedDelayedCarrier.canonicalDeferredClose]
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOne]
  rw [hselectedOneFlag]
  simp only [Bool.false_eq_true, ↓reduceIte]
  calc
    _ = (freshTwo.2.tag A strategy hwin true).1 := hselectedTwo
    _ = profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
          strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentTwo
            A strategy hwin
            (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
              A strategy hwin fallback.1 one)
            (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
              A strategy hwin fallback.2 two))
          (.simultaneous (inputOne, inputTwo)) := hfreshTwo
    _ = _ := by rw [hparentEq]

/-- Exact strict-right equation of the repaired authority trace. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowParentOneAt_succ_of_right
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (hgraph : (env n).graph = .right) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowParentOneAt
        A strategy hwin initialTag env (n + 1) =
      let fallback :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
          A strategy hwin initialTag
      let pair :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSemanticPairAt
          A strategy hwin initialTag env n
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowReceivedTwo
        A strategy hwin fallback pair.2 (env n).inputTwo pair.1
          (env n).inputOne).child A strategy hwin := by
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin initialTag
  let pair :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSemanticPairAt
      A strategy hwin initialTag env n
  have hpending :=
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSemanticPairAt_invariant
      A strategy hwin initialTag env n).1
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowParentOneAt,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSemanticPairAt,
    FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
    hgraph]
  exact phaseRestartRowParentOne_strictRight A strategy hwin fallback pair.1
    (env n).inputOne pair.2 (env n).inputTwo hpending

/-- Exact strict-left mirror. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowParentOneAt_succ_of_left
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (hgraph : (env n).graph = .left) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowParentOneAt
        A strategy hwin initialTag env (n + 1) =
      let fallback :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
          A strategy hwin initialTag
      let pair :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSemanticPairAt
          A strategy hwin initialTag env n
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowReceivedOne
        A strategy hwin fallback pair.1 (env n).inputOne pair.2
          (env n).inputTwo).child A strategy hwin := by
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin initialTag
  let pair :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSemanticPairAt
      A strategy hwin initialTag env n
  have hpending :=
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSemanticPairAt_invariant
      A strategy hwin initialTag env n).1
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowParentOneAt,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSemanticPairAt,
    FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
    hgraph]
  exact phaseRestartRowParentOne_strictLeft A strategy hwin fallback pair.1
    (env n).inputOne pair.2 (env n).inputTwo hpending

/-- Exact simultaneous child of the repaired authority trace. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowParentOneAt_succ_of_both
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (hgraph : (env n).graph = .both) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowParentOneAt
        A strategy hwin initialTag env (n + 1) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
        hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowParentOneAt
          A strategy hwin initialTag env n)
        (.simultaneous ((env n).inputOne, (env n).inputTwo)) := by
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin initialTag
  let pair :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSemanticPairAt
      A strategy hwin initialTag env n
  have hinvariant :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSemanticPairAt_invariant
      A strategy hwin initialTag env n
  have hparents :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentsAgree_of_selectedAuthorityCompatible
      A strategy hwin fallback pair.1 pair.2 hinvariant.2
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowParentOneAt,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSemanticPairAt,
    FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
    hgraph]
  exact phaseRestartRowParentOne_both A strategy hwin fallback pair.1
    (env n).inputOne pair.2 (env n).inputTwo hparents

@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowParentOneAt_zero
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowParentOneAt
      A strategy hwin initialTag env 0 = initialTag.1 := by
  rfl

/-! ## Selected phase bases along the semantic trace -/

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSelectedOneAt
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    LinkedOne A strategy hwin :=
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin initialTag
  let pair :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSemanticPairAt
      A strategy hwin initialTag env n
  profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
    A strategy hwin fallback.1 pair.1

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSelectedTwoAt
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    LinkedTwo A strategy hwin :=
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin initialTag
  let pair :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSemanticPairAt
      A strategy hwin initialTag env n
  profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
    A strategy hwin fallback.2 pair.2

/-- The endpoint-local receive bits of the repaired trace, exposed through
the controller-independent operational-cut interface. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowReceivePhaseBits
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) :
    OperationalReceivePhaseBits (fun n ↦ (env n).graph) where
  one := fun n ↦
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSelectedOneAt
      A strategy hwin initialTag env n).2.1
  two := fun n ↦
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSelectedTwoAt
      A strategy hwin initialTag env n).2.1
  initial := by
    exact
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSemanticPairAt_zero_selected_lastRecv
        A strategy hwin initialTag env
  step := by
    intro n
    exact
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSemanticPairAt_succ_selected_lastRecv
        A strategy hwin initialTag env n

/-- The local process-two bit selects the canonical row at every completed
strict-right operational block. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowRightClosingRow_eq
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (k : Nat) (hgraph : (env (cuts.cuts k)).graph = .right) :
    (if
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSelectedTwoAt
          A strategy hwin initialTag env
            (cuts.cuts k + cuts.openLength k)).2.1
      then PairedEntryRow.both else PairedEntryRow.first) =
        OperationalCloseCutPackage.bankOperationalRowAt cuts k := by
  exact
    OperationalReceivePhaseBits.right_closing_row_eq_bankOperationalRowAt
      cuts
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowReceivePhaseBits
        A strategy hwin initialTag env)
      k hgraph

/-- Process-one strict-left mirror. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowLeftClosingRow_eq
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (k : Nat) (hgraph : (env (cuts.cuts k)).graph = .left) :
    (if
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSelectedOneAt
          A strategy hwin initialTag env
            (cuts.cuts k + cuts.openLength k)).2.1
      then PairedEntryRow.both else PairedEntryRow.first) =
        OperationalCloseCutPackage.bankOperationalRowAt cuts k := by
  exact
    OperationalReceivePhaseBits.left_closing_row_eq_bankOperationalRowAt
      cuts
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowReceivePhaseBits
        A strategy hwin initialTag env)
      k hgraph

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowRightBaseAt
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :=
  profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightBase
    A strategy hwin
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSelectedOneAt
        A strategy hwin initialTag env n)
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSelectedTwoAt
        A strategy hwin initialTag env n)

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowLeftBaseAt
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :=
  profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftBase
    A strategy hwin
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSelectedOneAt
        A strategy hwin initialTag env n)
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSelectedTwoAt
        A strategy hwin initialTag env n)

def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowRightPairRootedAt
    (root : BankControl A strategy hwin)
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) : Prop :=
  let base :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowRightBaseAt
      A strategy hwin initialTag env n
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairAtPrefix
    A strategy hwin root base.1.1 base.1.2

def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowLeftPairRootedAt
    (root : BankControl A strategy hwin)
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) : Prop :=
  let base :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowLeftBaseAt
      A strategy hwin initialTag env n
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairAtPrefix
    A strategy hwin root base.2.1 base.2.2

/-! ## One-round preservation of a fixed block root -/

private theorem phaseRestartRowSelectedRightBase_strictRight
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (one : FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
      (LinkedOne A strategy hwin) (Payload A strategy hwin))
    (two : FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
      (LinkedTwo A strategy hwin) (Payload A strategy hwin))
    (input : In₁ × In₂) :
    let nextOne :=
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvOne
        A strategy hwin (.inl one : OneControl A strategy hwin) input.1).1
    let nextTwo :=
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowOpenRecvTwo
        A strategy hwin fallback (.inl two : TwoControl A strategy hwin)
          input.2 (.inl one : OneControl A strategy hwin) input.1).1
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightBase
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
            A strategy hwin fallback.1 nextOne)
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
            A strategy hwin fallback.2 nextTwo) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayAdvance
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightBase
            A strategy hwin
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
                A strategy hwin fallback.1 (.inl one))
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
                A strategy hwin fallback.2 (.inl two))) input := by
  rcases one with ⟨memberOne, sharedOne, payloadOne⟩
  rcases two with ⟨memberTwo, sharedTwo, payloadTwo⟩
  cases memberOne <;> cases memberTwo <;> rfl

private theorem phaseRestartRowSelectedLeftBase_strictLeft
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (one : FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
      (LinkedOne A strategy hwin) (Payload A strategy hwin))
    (two : FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
      (LinkedTwo A strategy hwin) (Payload A strategy hwin))
    (input : In₁ × In₂) :
    let nextOne :=
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowOpenRecvOne
        A strategy hwin fallback (.inl one : OneControl A strategy hwin)
          input.1 (.inl two : TwoControl A strategy hwin) input.2).1
    let nextTwo :=
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvTwo
        A strategy hwin (.inl two : TwoControl A strategy hwin) input.2).1
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftBase
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
            A strategy hwin fallback.1 nextOne)
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
            A strategy hwin fallback.2 nextTwo) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayAdvance
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftBase
            A strategy hwin
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
                A strategy hwin fallback.1 (.inl one))
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
                A strategy hwin fallback.2 (.inl two))) input := by
  rcases one with ⟨memberOne, sharedOne, payloadOne⟩
  rcases two with ⟨memberTwo, sharedTwo, payloadTwo⟩
  cases memberOne <;> cases memberTwo <;> rfl

theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowRightPairRootedAt.step
    {root : BankControl A strategy hwin}
    {initialTag : RetainedTag A strategy hwin}
    {env : EnvironmentSequence In₁ In₂} {n : Nat}
    (hpair :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowRightPairRootedAt
        A strategy hwin root initialTag env n)
    (hgraph : (env n).graph = .right) :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowRightPairRootedAt
      A strategy hwin root initialTag env (n + 1) := by
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin initialTag
  let pair :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSemanticPairAt
      A strategy hwin initialTag env n
  have hpending :=
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSemanticPairAt_invariant
      A strategy hwin initialTag env n).1
  change FiniteAcknowledgedDelayedCarrier.DeferredPairIsPending pair.1 pair.2
    at hpending
  cases hone : pair.1 with
  | inr recurrent => exact False.elim (by simpa [hone] using hpending.1)
  | inl onePending =>
      cases htwo : pair.2 with
      | inr recurrent => exact False.elim (by simpa [htwo] using hpending.2)
      | inl twoPending =>
          have hnext :
              profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSemanticPairAt
                  A strategy hwin initialTag env (n + 1) =
                ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvOne
                    A strategy hwin pair.1 (env n).inputOne).1,
                  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowOpenRecvTwo
                    A strategy hwin fallback pair.2 (env n).inputTwo pair.1
                      (env n).inputOne).1) := by
            rw [
              profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSemanticPairAt,
              FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
              hgraph]
            rfl
          have hbase :
              profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowRightBaseAt
                  A strategy hwin initialTag env (n + 1) =
                profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayAdvance
                  A strategy hwin
                    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowRightBaseAt
                      A strategy hwin initialTag env n)
                    ((env n).inputOne, (env n).inputTwo) := by
            simp only [
              profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowRightBaseAt,
              profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSelectedOneAt,
              profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSelectedTwoAt]
            rw [hnext]
            rw [hone, htwo]
            exact phaseRestartRowSelectedRightBase_strictRight A strategy hwin
              fallback onePending twoPending
                ((env n).inputOne, (env n).inputTwo)
          change
            ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairAtPrefix
              A strategy hwin root
                (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowRightBaseAt
                  A strategy hwin initialTag env (n + 1)).1.1
                (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowRightBaseAt
                  A strategy hwin initialTag env (n + 1)).1.2
          change
            ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairAtPrefix
              A strategy hwin root
                (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowRightBaseAt
                  A strategy hwin initialTag env n).1.1
                (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowRightBaseAt
                  A strategy hwin initialTag env n).1.2 at hpair
          rw [hbase]
          simpa [
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayAdvance]
            using hpair.step A strategy hwin
              ((env n).inputTwo, (env n).inputOne)

theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowLeftPairRootedAt.step
    {root : BankControl A strategy hwin}
    {initialTag : RetainedTag A strategy hwin}
    {env : EnvironmentSequence In₁ In₂} {n : Nat}
    (hpair :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowLeftPairRootedAt
        A strategy hwin root initialTag env n)
    (hgraph : (env n).graph = .left) :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowLeftPairRootedAt
      A strategy hwin root initialTag env (n + 1) := by
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin initialTag
  let pair :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSemanticPairAt
      A strategy hwin initialTag env n
  have hpending :=
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSemanticPairAt_invariant
      A strategy hwin initialTag env n).1
  change FiniteAcknowledgedDelayedCarrier.DeferredPairIsPending pair.1 pair.2
    at hpending
  cases hone : pair.1 with
  | inr recurrent => exact False.elim (by simpa [hone] using hpending.1)
  | inl onePending =>
      cases htwo : pair.2 with
      | inr recurrent => exact False.elim (by simpa [htwo] using hpending.2)
      | inl twoPending =>
          have hnext :
              profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSemanticPairAt
                  A strategy hwin initialTag env (n + 1) =
                ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowOpenRecvOne
                    A strategy hwin fallback pair.1 (env n).inputOne pair.2
                      (env n).inputTwo).1,
                  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvTwo
                    A strategy hwin pair.2 (env n).inputTwo).1) := by
            rw [
              profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSemanticPairAt,
              FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
              hgraph]
            rfl
          have hbase :
              profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowLeftBaseAt
                  A strategy hwin initialTag env (n + 1) =
                profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayAdvance
                  A strategy hwin
                    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowLeftBaseAt
                      A strategy hwin initialTag env n)
                    ((env n).inputOne, (env n).inputTwo) := by
            simp only [
              profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowLeftBaseAt,
              profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSelectedOneAt,
              profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSelectedTwoAt]
            rw [hnext]
            rw [hone, htwo]
            exact phaseRestartRowSelectedLeftBase_strictLeft A strategy hwin
              fallback onePending twoPending
                ((env n).inputOne, (env n).inputTwo)
          change
            ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairAtPrefix
              A strategy hwin root
                (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowLeftBaseAt
                  A strategy hwin initialTag env (n + 1)).2.1
                (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowLeftBaseAt
                  A strategy hwin initialTag env (n + 1)).2.2
          change
            ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairAtPrefix
              A strategy hwin root
                (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowLeftBaseAt
                  A strategy hwin initialTag env n).2.1
                (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowLeftBaseAt
                  A strategy hwin initialTag env n).2.2 at hpair
          rw [hbase]
          simpa [
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayAdvance]
            using hpair.step A strategy hwin
              ((env n).inputOne, (env n).inputTwo)

/-! ## Public same-block relay recurrences -/

/-- During a strict-right block, the complete row-aware selected relay is
the ordinary linked-table advance of the preceding relay. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowRightBaseAt_succ_of_right_eq_advance
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (hgraph : (env n).graph = .right) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowRightBaseAt
        A strategy hwin initialTag env (n + 1) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayAdvance
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowRightBaseAt
            A strategy hwin initialTag env n)
          ((env n).inputOne, (env n).inputTwo) := by
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin initialTag
  let pair :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSemanticPairAt
      A strategy hwin initialTag env n
  have hpending :=
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSemanticPairAt_invariant
      A strategy hwin initialTag env n).1
  change FiniteAcknowledgedDelayedCarrier.DeferredPairIsPending pair.1 pair.2
    at hpending
  cases hone : pair.1 with
  | inr recurrent => exact False.elim (by simpa [hone] using hpending.1)
  | inl onePending =>
      cases htwo : pair.2 with
      | inr recurrent => exact False.elim (by simpa [htwo] using hpending.2)
      | inl twoPending =>
          have hnext :
              profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSemanticPairAt
                  A strategy hwin initialTag env (n + 1) =
                ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvOne
                    A strategy hwin pair.1 (env n).inputOne).1,
                  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowOpenRecvTwo
                    A strategy hwin fallback pair.2 (env n).inputTwo pair.1
                      (env n).inputOne).1) := by
            rw [
              profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSemanticPairAt,
              FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
              hgraph]
            rfl
          simp only [
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowRightBaseAt,
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSelectedOneAt,
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSelectedTwoAt]
          rw [hnext, hone, htwo]
          exact phaseRestartRowSelectedRightBase_strictRight A strategy hwin
            fallback onePending twoPending
              ((env n).inputOne, (env n).inputTwo)

/-- Strict-left mirror of the complete relay recurrence. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowLeftBaseAt_succ_of_left_eq_advance
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (hgraph : (env n).graph = .left) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowLeftBaseAt
        A strategy hwin initialTag env (n + 1) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayAdvance
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowLeftBaseAt
            A strategy hwin initialTag env n)
          ((env n).inputOne, (env n).inputTwo) := by
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin initialTag
  let pair :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSemanticPairAt
      A strategy hwin initialTag env n
  have hpending :=
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSemanticPairAt_invariant
      A strategy hwin initialTag env n).1
  change FiniteAcknowledgedDelayedCarrier.DeferredPairIsPending pair.1 pair.2
    at hpending
  cases hone : pair.1 with
  | inr recurrent => exact False.elim (by simpa [hone] using hpending.1)
  | inl onePending =>
      cases htwo : pair.2 with
      | inr recurrent => exact False.elim (by simpa [htwo] using hpending.2)
      | inl twoPending =>
          have hnext :
              profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSemanticPairAt
                  A strategy hwin initialTag env (n + 1) =
                ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowOpenRecvOne
                    A strategy hwin fallback pair.1 (env n).inputOne pair.2
                      (env n).inputTwo).1,
                  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvTwo
                    A strategy hwin pair.2 (env n).inputTwo).1) := by
            rw [
              profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSemanticPairAt,
              FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
              hgraph]
            rfl
          simp only [
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowLeftBaseAt,
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSelectedOneAt,
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowSelectedTwoAt]
          rw [hnext, hone, htwo]
          exact phaseRestartRowSelectedLeftBase_strictLeft A strategy hwin
            fallback onePending twoPending
              ((env n).inputOne, (env n).inputTwo)

/-! ## Finite open-block propagation -/

/-- A right pair rooted at the bank state at a cut remains rooted there
through every nonclosing round of that maximal right block. -/
theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowRightPairRootedAt.propagate_open
    {root : BankControl A strategy hwin}
    {initialTag : RetainedTag A strategy hwin}
    {env : EnvironmentSequence In₁ In₂}
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (k : Nat)
    (hgraph : (env (cuts.cuts k)).graph = .right)
    (hpair :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowRightPairRootedAt
        A strategy hwin root initialTag env (cuts.cuts k)) :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowRightPairRootedAt
      A strategy hwin root initialTag env
        (cuts.cuts k + cuts.openLength k) := by
  apply
    DistributedSynthesis.DetParityAutomaton.OperationalCloseCutPackage.propagate_homogeneous_open
      cuts
    (P := fun n ↦
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowRightPairRootedAt
        A strategy hwin root initialTag env n) k
  · intro n hcurrent hsame
    exact hcurrent.step A strategy hwin (hsame.trans hgraph)
  · exact hpair

/-- Left mirror. -/
theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowLeftPairRootedAt.propagate_open
    {root : BankControl A strategy hwin}
    {initialTag : RetainedTag A strategy hwin}
    {env : EnvironmentSequence In₁ In₂}
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (k : Nat)
    (hgraph : (env (cuts.cuts k)).graph = .left)
    (hpair :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowLeftPairRootedAt
        A strategy hwin root initialTag env (cuts.cuts k)) :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowLeftPairRootedAt
      A strategy hwin root initialTag env
        (cuts.cuts k + cuts.openLength k) := by
  apply
    DistributedSynthesis.DetParityAutomaton.OperationalCloseCutPackage.propagate_homogeneous_open
      cuts
    (P := fun n ↦
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowLeftPairRootedAt
        A strategy hwin root initialTag env n) k
  · intro n hcurrent hsame
    exact hcurrent.step A strategy hwin (hsame.trans hgraph)
  · exact hpair

end

end DetParityAutomaton

end DistributedSynthesis
