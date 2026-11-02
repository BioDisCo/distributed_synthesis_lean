/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartController
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
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartParentOneAt
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    BankControl A strategy hwin :=
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin initialTag
  let pair :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartSemanticPairAt
      A strategy hwin initialTag env n
  profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOne
    A strategy hwin
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
        A strategy hwin fallback.1 pair.1)
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
        A strategy hwin fallback.2 pair.2)

/-- Process-two mirror of the repaired authority coordinate. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartParentTwoAt
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    BankControl A strategy hwin :=
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin initialTag
  let pair :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartSemanticPairAt
      A strategy hwin initialTag env n
  profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentTwo
    A strategy hwin
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
        A strategy hwin fallback.1 pair.1)
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
        A strategy hwin fallback.2 pair.2)

theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartParentsAt_eq
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartParentOneAt
        A strategy hwin initialTag env n =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartParentTwoAt
        A strategy hwin initialTag env n := by
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin initialTag
  let pair :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartSemanticPairAt
      A strategy hwin initialTag env n
  have hinvariant :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartSemanticPairAt_invariant
      A strategy hwin initialTag env n
  exact
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentsAgree_of_selectedAuthorityCompatible
      A strategy hwin fallback pair.1 pair.2 hinvariant.2

/-! ## Round-local authority equations -/

private theorem phaseRestartParentOne_strictRight
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (one : OneControl A strategy hwin) (inputOne : In₁)
    (two : TwoControl A strategy hwin) (inputTwo : In₂)
    (hpending :
      FiniteAcknowledgedDelayedCarrier.DeferredPairIsPending one two) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOne
        A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
          A strategy hwin fallback.1
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredNoRecvOne
            A strategy hwin one inputOne).1)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
          A strategy hwin fallback.2
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvTwo
            A strategy hwin fallback two inputTwo one inputOne).1) =
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartReceivedTwo
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
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne_noRecv_lastRecv,
            Bool.false_eq_true, ↓reduceIte]
          rfl

private theorem phaseRestartParentOne_strictLeft
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (one : OneControl A strategy hwin) (inputOne : In₁)
    (two : TwoControl A strategy hwin) (inputTwo : In₂)
    (hpending :
      FiniteAcknowledgedDelayedCarrier.DeferredPairIsPending one two) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOne
        A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
          A strategy hwin fallback.1
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne
            A strategy hwin fallback one inputOne two inputTwo).1)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
          A strategy hwin fallback.2
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredNoRecvTwo
            A strategy hwin two inputTwo).1) =
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartReceivedOne
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
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartSelectedOne_openRecv_lastRecv,
            ↓reduceIte]
          rfl

private theorem phaseRestartParentOne_both
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (one : OneControl A strategy hwin) (inputOne : In₁)
    (two : TwoControl A strategy hwin) (inputTwo : In₂)
    (hparents :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentsAgree
        A strategy hwin fallback one two) :
    let next :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartClose
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
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartFreshOne
      A strategy hwin fallback one inputOne two inputTwo
  let freshTwo :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartFreshTwo
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
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartFreshTwo_closed_child
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
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartClose,
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
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartParentOneAt_succ_of_right
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (hgraph : (env n).graph = .right) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartParentOneAt
        A strategy hwin initialTag env (n + 1) =
      let fallback :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
          A strategy hwin initialTag
      let pair :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartSemanticPairAt
          A strategy hwin initialTag env n
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartReceivedTwo
        A strategy hwin fallback pair.2 (env n).inputTwo pair.1
          (env n).inputOne).child A strategy hwin := by
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin initialTag
  let pair :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartSemanticPairAt
      A strategy hwin initialTag env n
  have hpending :=
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartSemanticPairAt_invariant
      A strategy hwin initialTag env n).1
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartParentOneAt,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartSemanticPairAt,
    FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
    hgraph]
  exact phaseRestartParentOne_strictRight A strategy hwin fallback pair.1
    (env n).inputOne pair.2 (env n).inputTwo hpending

/-- Exact strict-left mirror. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartParentOneAt_succ_of_left
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (hgraph : (env n).graph = .left) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartParentOneAt
        A strategy hwin initialTag env (n + 1) =
      let fallback :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
          A strategy hwin initialTag
      let pair :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartSemanticPairAt
          A strategy hwin initialTag env n
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartReceivedOne
        A strategy hwin fallback pair.1 (env n).inputOne pair.2
          (env n).inputTwo).child A strategy hwin := by
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin initialTag
  let pair :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartSemanticPairAt
      A strategy hwin initialTag env n
  have hpending :=
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartSemanticPairAt_invariant
      A strategy hwin initialTag env n).1
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartParentOneAt,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartSemanticPairAt,
    FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
    hgraph]
  exact phaseRestartParentOne_strictLeft A strategy hwin fallback pair.1
    (env n).inputOne pair.2 (env n).inputTwo hpending

/-- Exact simultaneous child of the repaired authority trace. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartParentOneAt_succ_of_both
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (hgraph : (env n).graph = .both) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartParentOneAt
        A strategy hwin initialTag env (n + 1) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
        hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartParentOneAt
          A strategy hwin initialTag env n)
        (.simultaneous ((env n).inputOne, (env n).inputTwo)) := by
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin initialTag
  let pair :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartSemanticPairAt
      A strategy hwin initialTag env n
  have hinvariant :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartSemanticPairAt_invariant
      A strategy hwin initialTag env n
  have hparents :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentsAgree_of_selectedAuthorityCompatible
      A strategy hwin fallback pair.1 pair.2 hinvariant.2
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartParentOneAt,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartSemanticPairAt,
    FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
    hgraph]
  exact phaseRestartParentOne_both A strategy hwin fallback pair.1
    (env n).inputOne pair.2 (env n).inputTwo hparents

@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartParentOneAt_zero
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartParentOneAt
      A strategy hwin initialTag env 0 = initialTag.1 := by
  rfl

/-! ## Selected phase bases along the semantic trace -/

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartSelectedOneAt
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    LinkedOne A strategy hwin :=
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin initialTag
  let pair :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartSemanticPairAt
      A strategy hwin initialTag env n
  profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
    A strategy hwin fallback.1 pair.1

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartSelectedTwoAt
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    LinkedTwo A strategy hwin :=
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin initialTag
  let pair :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartSemanticPairAt
      A strategy hwin initialTag env n
  profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
    A strategy hwin fallback.2 pair.2

/-- The endpoint-local receive bits of the repaired trace, exposed through
the controller-independent operational-cut interface. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartReceivePhaseBits
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) :
    OperationalReceivePhaseBits (fun n ↦ (env n).graph) where
  one := fun n ↦
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartSelectedOneAt
      A strategy hwin initialTag env n).2.1
  two := fun n ↦
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartSelectedTwoAt
      A strategy hwin initialTag env n).2.1
  initial := by
    exact
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartSemanticPairAt_zero_selected_lastRecv
        A strategy hwin initialTag env
  step := by
    intro n
    exact
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartSemanticPairAt_succ_selected_lastRecv
        A strategy hwin initialTag env n

/-- The local process-two bit selects the canonical row at every completed
strict-right operational block. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightClosingRow_eq
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (k : Nat) (hgraph : (env (cuts.cuts k)).graph = .right) :
    (if
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartSelectedTwoAt
          A strategy hwin initialTag env
            (cuts.cuts k + cuts.openLength k)).2.1
      then PairedEntryRow.both else PairedEntryRow.first) =
        OperationalCloseCutPackage.bankOperationalRowAt cuts k := by
  exact
    OperationalReceivePhaseBits.right_closing_row_eq_bankOperationalRowAt
      cuts
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartReceivePhaseBits
        A strategy hwin initialTag env)
      k hgraph

/-- Process-one strict-left mirror. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftClosingRow_eq
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (k : Nat) (hgraph : (env (cuts.cuts k)).graph = .left) :
    (if
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartSelectedOneAt
          A strategy hwin initialTag env
            (cuts.cuts k + cuts.openLength k)).2.1
      then PairedEntryRow.both else PairedEntryRow.first) =
        OperationalCloseCutPackage.bankOperationalRowAt cuts k := by
  exact
    OperationalReceivePhaseBits.left_closing_row_eq_bankOperationalRowAt
      cuts
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartReceivePhaseBits
        A strategy hwin initialTag env)
      k hgraph

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightBaseAt
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :=
  profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightBase
    A strategy hwin
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartSelectedOneAt
        A strategy hwin initialTag env n)
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartSelectedTwoAt
        A strategy hwin initialTag env n)

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftBaseAt
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :=
  profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftBase
    A strategy hwin
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartSelectedOneAt
        A strategy hwin initialTag env n)
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartSelectedTwoAt
        A strategy hwin initialTag env n)

def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightPairRootedAt
    (root : BankControl A strategy hwin)
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) : Prop :=
  let base :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightBaseAt
      A strategy hwin initialTag env n
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairAtPrefix
    A strategy hwin root base.1.1 base.1.2

def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftPairRootedAt
    (root : BankControl A strategy hwin)
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) : Prop :=
  let base :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftBaseAt
      A strategy hwin initialTag env n
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairAtPrefix
    A strategy hwin root base.2.1 base.2.2

/-! ## One-round preservation of a fixed block root -/

private theorem phaseRestartSelectedRightBase_strictRight
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (one : FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
      (LinkedOne A strategy hwin) (Payload A strategy hwin))
    (two : FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
      (LinkedTwo A strategy hwin) (Payload A strategy hwin))
    (input : In₁ × In₂) :
    let nextOne :=
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredNoRecvOne
        A strategy hwin (.inl one : OneControl A strategy hwin) input.1).1
    let nextTwo :=
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvTwo
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

private theorem phaseRestartSelectedLeftBase_strictLeft
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (one : FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
      (LinkedOne A strategy hwin) (Payload A strategy hwin))
    (two : FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
      (LinkedTwo A strategy hwin) (Payload A strategy hwin))
    (input : In₁ × In₂) :
    let nextOne :=
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne
        A strategy hwin fallback (.inl one : OneControl A strategy hwin)
          input.1 (.inl two : TwoControl A strategy hwin) input.2).1
    let nextTwo :=
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredNoRecvTwo
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
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightPairRootedAt.step
    {root : BankControl A strategy hwin}
    {initialTag : RetainedTag A strategy hwin}
    {env : EnvironmentSequence In₁ In₂} {n : Nat}
    (hpair :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightPairRootedAt
        A strategy hwin root initialTag env n)
    (hgraph : (env n).graph = .right) :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightPairRootedAt
      A strategy hwin root initialTag env (n + 1) := by
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin initialTag
  let pair :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartSemanticPairAt
      A strategy hwin initialTag env n
  have hpending :=
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartSemanticPairAt_invariant
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
              profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartSemanticPairAt
                  A strategy hwin initialTag env (n + 1) =
                ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredNoRecvOne
                    A strategy hwin pair.1 (env n).inputOne).1,
                  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvTwo
                    A strategy hwin fallback pair.2 (env n).inputTwo pair.1
                      (env n).inputOne).1) := by
            rw [
              profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartSemanticPairAt,
              FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
              hgraph]
            rfl
          have hbase :
              profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightBaseAt
                  A strategy hwin initialTag env (n + 1) =
                profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayAdvance
                  A strategy hwin
                    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightBaseAt
                      A strategy hwin initialTag env n)
                    ((env n).inputOne, (env n).inputTwo) := by
            simp only [
              profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightBaseAt,
              profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartSelectedOneAt,
              profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartSelectedTwoAt]
            rw [hnext]
            rw [hone, htwo]
            exact phaseRestartSelectedRightBase_strictRight A strategy hwin
              fallback onePending twoPending
                ((env n).inputOne, (env n).inputTwo)
          change
            ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairAtPrefix
              A strategy hwin root
                (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightBaseAt
                  A strategy hwin initialTag env (n + 1)).1.1
                (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightBaseAt
                  A strategy hwin initialTag env (n + 1)).1.2
          change
            ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairAtPrefix
              A strategy hwin root
                (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightBaseAt
                  A strategy hwin initialTag env n).1.1
                (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightBaseAt
                  A strategy hwin initialTag env n).1.2 at hpair
          rw [hbase]
          simpa [
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayAdvance]
            using hpair.step A strategy hwin
              ((env n).inputTwo, (env n).inputOne)

theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftPairRootedAt.step
    {root : BankControl A strategy hwin}
    {initialTag : RetainedTag A strategy hwin}
    {env : EnvironmentSequence In₁ In₂} {n : Nat}
    (hpair :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftPairRootedAt
        A strategy hwin root initialTag env n)
    (hgraph : (env n).graph = .left) :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftPairRootedAt
      A strategy hwin root initialTag env (n + 1) := by
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin initialTag
  let pair :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartSemanticPairAt
      A strategy hwin initialTag env n
  have hpending :=
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartSemanticPairAt_invariant
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
              profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartSemanticPairAt
                  A strategy hwin initialTag env (n + 1) =
                ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne
                    A strategy hwin fallback pair.1 (env n).inputOne pair.2
                      (env n).inputTwo).1,
                  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredNoRecvTwo
                    A strategy hwin pair.2 (env n).inputTwo).1) := by
            rw [
              profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartSemanticPairAt,
              FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
              hgraph]
            rfl
          have hbase :
              profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftBaseAt
                  A strategy hwin initialTag env (n + 1) =
                profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayAdvance
                  A strategy hwin
                    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftBaseAt
                      A strategy hwin initialTag env n)
                    ((env n).inputOne, (env n).inputTwo) := by
            simp only [
              profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftBaseAt,
              profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartSelectedOneAt,
              profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartSelectedTwoAt]
            rw [hnext]
            rw [hone, htwo]
            exact phaseRestartSelectedLeftBase_strictLeft A strategy hwin
              fallback onePending twoPending
                ((env n).inputOne, (env n).inputTwo)
          change
            ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairAtPrefix
              A strategy hwin root
                (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftBaseAt
                  A strategy hwin initialTag env (n + 1)).2.1
                (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftBaseAt
                  A strategy hwin initialTag env (n + 1)).2.2
          change
            ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairAtPrefix
              A strategy hwin root
                (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftBaseAt
                  A strategy hwin initialTag env n).2.1
                (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftBaseAt
                  A strategy hwin initialTag env n).2.2 at hpair
          rw [hbase]
          simpa [
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayAdvance]
            using hpair.step A strategy hwin
              ((env n).inputOne, (env n).inputTwo)

/-! ## Finite open-block propagation -/

/-- A right pair rooted at the bank state at a cut remains rooted there
through every nonclosing round of that maximal right block. -/
theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightPairRootedAt.propagate_open
    {root : BankControl A strategy hwin}
    {initialTag : RetainedTag A strategy hwin}
    {env : EnvironmentSequence In₁ In₂}
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (k : Nat)
    (hgraph : (env (cuts.cuts k)).graph = .right)
    (hpair :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightPairRootedAt
        A strategy hwin root initialTag env (cuts.cuts k)) :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightPairRootedAt
      A strategy hwin root initialTag env
        (cuts.cuts k + cuts.openLength k) := by
  apply
    DistributedSynthesis.DetParityAutomaton.OperationalCloseCutPackage.propagate_homogeneous_open
      cuts
    (P := fun n ↦
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightPairRootedAt
        A strategy hwin root initialTag env n) k
  · intro n hcurrent hsame
    exact hcurrent.step A strategy hwin (hsame.trans hgraph)
  · exact hpair

/-- Left mirror. -/
theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftPairRootedAt.propagate_open
    {root : BankControl A strategy hwin}
    {initialTag : RetainedTag A strategy hwin}
    {env : EnvironmentSequence In₁ In₂}
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (k : Nat)
    (hgraph : (env (cuts.cuts k)).graph = .left)
    (hpair :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftPairRootedAt
        A strategy hwin root initialTag env (cuts.cuts k)) :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftPairRootedAt
      A strategy hwin root initialTag env
        (cuts.cuts k + cuts.openLength k) := by
  apply
    DistributedSynthesis.DetParityAutomaton.OperationalCloseCutPackage.propagate_homogeneous_open
      cuts
    (P := fun n ↦
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftPairRootedAt
        A strategy hwin root initialTag env n) k
  · intro n hcurrent hsame
    exact hcurrent.step A strategy hwin (hsame.trans hgraph)
  · exact hpair

end

end DetParityAutomaton

end DistributedSynthesis
