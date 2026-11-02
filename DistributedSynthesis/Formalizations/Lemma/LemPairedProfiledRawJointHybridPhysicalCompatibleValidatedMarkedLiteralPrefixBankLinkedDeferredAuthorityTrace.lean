/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankLinkedDeferredMemberController

/-!
# The authoritative bank coordinate of the linked deferred trace

The acknowledged linked controller has two locally stored bank coordinates.
The dangerous-pair invariant proves that the endpoint-local authority rules
select one common parent.  This file names that parent along the canonical
semantic trace and exposes the equality of the two local selections.

This is the state-level bridge needed by the later direction-path readback.
It introduces no graph, orientation, leader, or strict-leader input into an
executable transition: the environment occurs only in this proof-side trace.
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

/-- The initial linked pair, reused as the total fallback of the semantic
trace. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredTraceFallback
    (initialTag : RetainedTag A strategy hwin) :
    LinkedOne A strategy hwin × LinkedTwo A strategy hwin :=
  profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
    A strategy hwin initialTag

/-- Canonical proof-side control pair before round `n`. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSemanticPairAt
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    OneControl A strategy hwin × TwoControl A strategy hwin :=
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredTraceFallback
      A strategy hwin initialTag
  FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace
    (.inl
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialOne
        A strategy hwin initialTag) : OneControl A strategy hwin)
    (.inl
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialTwo
        A strategy hwin initialTag) : TwoControl A strategy hwin)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredNoRecvOne
      A strategy hwin)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredNoRecvTwo
      A strategy hwin)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredOpenRecvOne
      A strategy hwin fallback)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredOpenRecvTwo
      A strategy hwin fallback)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredClose
      A strategy hwin fallback) env n

/-- Process one's receive-normalized local bank parent at time `n`. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOneAt
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    BankControl A strategy hwin :=
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredTraceFallback
      A strategy hwin initialTag
  let pair :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSemanticPairAt
      A strategy hwin initialTag env n
  profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOne
    A strategy hwin
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
        A strategy hwin fallback.1 pair.1)
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
        A strategy hwin fallback.2 pair.2)

/-- Process-two mirror of the authority selection. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentTwoAt
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    BankControl A strategy hwin :=
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredTraceFallback
      A strategy hwin initialTag
  let pair :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSemanticPairAt
      A strategy hwin initialTag env n
  profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentTwo
    A strategy hwin
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
        A strategy hwin fallback.1 pair.1)
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
        A strategy hwin fallback.2 pair.2)

/-- The canonical trace satisfies the full dangerous-pair invariant at every
time. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSemanticPairAt_invariant
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    let fallback :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredTraceFallback
        A strategy hwin initialTag
    let pair :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSemanticPairAt
        A strategy hwin initialTag env n
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPairInvariant
      A strategy hwin fallback pair.1 pair.2 := by
  dsimp only [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredTraceFallback,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSemanticPairAt]
  exact
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSemanticPairTrace_invariant
      A strategy hwin initialTag env n

/-- At every finite prefix, the two endpoint-local authority rules select the
same bank parent.  This is the trace-level form of the dangerous pair test. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentsAt_eq
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOneAt
        A strategy hwin initialTag env n =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentTwoAt
        A strategy hwin initialTag env n := by
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredTraceFallback
      A strategy hwin initialTag
  let pair :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSemanticPairAt
      A strategy hwin initialTag env n
  have hinvariant :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSemanticPairAt_invariant
      A strategy hwin initialTag env n
  exact
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentsAgree_of_selectedAuthorityCompatible
      A strategy hwin fallback pair.1 pair.2 hinvariant.2

/-! ## The three local graph cases at the authority coordinate -/

/-- In a strict-right round, the next authoritative coordinate is exactly the
child carried by process two's linked receiver. -/
private theorem
    linkedDeferredParentOne_strictRight
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
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredOpenRecvTwo
            A strategy hwin fallback two inputTwo one inputOne).1) =
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredReceivedTwo
        A strategy hwin fallback two inputTwo one inputOne).child A strategy
          hwin := by
  cases one with
  | inr recurrent =>
      exact False.elim hpending.1
  | inl onePending =>
      cases two with
      | inr recurrent =>
          exact False.elim hpending.2
      | inl twoPending =>
          simp only [
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOne,
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne_noRecv_lastRecv,
            Bool.false_eq_true, ↓reduceIte]
          rfl

/-- Strict-left mirror. -/
private theorem
    linkedDeferredParentOne_strictLeft
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (one : OneControl A strategy hwin) (inputOne : In₁)
    (two : TwoControl A strategy hwin) (inputTwo : In₂)
    (hpending :
      FiniteAcknowledgedDelayedCarrier.DeferredPairIsPending one two) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOne
        A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
          A strategy hwin fallback.1
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredOpenRecvOne
            A strategy hwin fallback one inputOne two inputTwo).1)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
          A strategy hwin fallback.2
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredNoRecvTwo
            A strategy hwin two inputTwo).1) =
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredReceivedOne
        A strategy hwin fallback one inputOne two inputTwo).child A strategy
          hwin := by
  cases one with
  | inr recurrent =>
      exact False.elim hpending.1
  | inl onePending =>
      cases two with
      | inr recurrent =>
          exact False.elim hpending.2
      | inl twoPending =>
          simp only [
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOne,
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne_openRecv_lastRecv,
            ↓reduceIte]
          rfl

/-- At a simultaneous receive, the closed interpretation installs the exact
simultaneous child of the common authoritative parent. -/
private theorem
    linkedDeferredParentOne_both
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (one : OneControl A strategy hwin) (inputOne : In₁)
    (two : TwoControl A strategy hwin) (inputTwo : In₂)
    (hparents :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentsAgree
        A strategy hwin fallback one two) :
    let next :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredClose
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
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFreshOne
      A strategy hwin fallback one inputOne two inputTwo
  let freshTwo :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFreshTwo
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
        ).2.1 = false :=
    rfl
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
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFreshTwo_closed_child
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
            A strategy hwin fallback.2 two) :=
    hparents.symm
  dsimp only [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredClose,
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

/-- The strict-right child visible at round `n`. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredStrictRightChildAt
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    BankControl A strategy hwin :=
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredTraceFallback
      A strategy hwin initialTag
  let pair :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSemanticPairAt
      A strategy hwin initialTag env n
  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredReceivedTwo
    A strategy hwin fallback pair.2 (env n).inputTwo pair.1
      (env n).inputOne).child A strategy hwin

/-- Strict-left mirror. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredStrictLeftChildAt
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    BankControl A strategy hwin :=
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredTraceFallback
      A strategy hwin initialTag
  let pair :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSemanticPairAt
      A strategy hwin initialTag env n
  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredReceivedOne
    A strategy hwin fallback pair.1 (env n).inputOne pair.2
      (env n).inputTwo).child A strategy hwin

/-- Exact state equation for a strict-right semantic trace step. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOneAt_succ_of_right
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (hgraph : (env n).graph = .right) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOneAt
        A strategy hwin initialTag env (n + 1) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredStrictRightChildAt
        A strategy hwin initialTag env n := by
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredTraceFallback
      A strategy hwin initialTag
  let pair :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSemanticPairAt
      A strategy hwin initialTag env n
  have hpending :=
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSemanticPairAt_invariant
      A strategy hwin initialTag env n).1
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOneAt,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSemanticPairAt,
    FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
    hgraph]
  exact
    linkedDeferredParentOne_strictRight A strategy hwin fallback pair.1
      (env n).inputOne pair.2 (env n).inputTwo hpending

/-- Exact state equation for a strict-left semantic trace step. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOneAt_succ_of_left
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (hgraph : (env n).graph = .left) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOneAt
        A strategy hwin initialTag env (n + 1) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredStrictLeftChildAt
        A strategy hwin initialTag env n := by
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredTraceFallback
      A strategy hwin initialTag
  let pair :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSemanticPairAt
      A strategy hwin initialTag env n
  have hpending :=
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSemanticPairAt_invariant
      A strategy hwin initialTag env n).1
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOneAt,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSemanticPairAt,
    FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
    hgraph]
  exact
    linkedDeferredParentOne_strictLeft A strategy hwin fallback pair.1
      (env n).inputOne pair.2 (env n).inputTwo hpending

/-- Exact simultaneous-successor equation on the canonical authority trace. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOneAt_succ_of_both
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (hgraph : (env n).graph = .both) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOneAt
        A strategy hwin initialTag env (n + 1) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
        hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOneAt
          A strategy hwin initialTag env n)
        (.simultaneous ((env n).inputOne, (env n).inputTwo)) := by
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredTraceFallback
      A strategy hwin initialTag
  let pair :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSemanticPairAt
      A strategy hwin initialTag env n
  have hinvariant :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSemanticPairAt_invariant
      A strategy hwin initialTag env n
  have hparents :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentsAgree_of_selectedAuthorityCompatible
      A strategy hwin fallback pair.1 pair.2 hinvariant.2
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOneAt,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSemanticPairAt,
    FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
    hgraph]
  exact
    linkedDeferredParentOne_both A strategy hwin fallback pair.1
      (env n).inputOne pair.2 (env n).inputTwo hparents

/-- The common authority coordinate begins at the retained tag's bank
state. -/
@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOneAt_zero
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOneAt
        A strategy hwin initialTag env 0 = initialTag.1 := by
  rfl

end

end DetParityAutomaton

end DistributedSynthesis
