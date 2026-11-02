/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridLinkedAcceptedOutputTail
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartCutOutput

/-!
# Homogeneous tails of the payload-linked FullRestart controller

An eventually homogeneous strict suffix is the final, unclosed operational
block and therefore is intentionally absent from the infinite close-cut
package.  This file handles it directly.  On repeated rounds of one strict
orientation, the receiver-selected full relay advances exactly once per
physical input pair.  The result is the same linked sender/receiver run used
by the accepted-tail theorem.
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

private abbrev LinkedRelay :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelay A
    strategy hwin

private abbrev RightSender :=
  ProfiledRawJointRightFinitePayloadLiteralPrefixSenderState A
    (BankControl A strategy hwin)

private abbrev RightReceiver :=
  ProfiledRawJointRightFinitePayloadLiteralPrefixReceiverState A
    (BankControl A strategy hwin)

private abbrev LeftSender :=
  ProfiledRawJointLeftFinitePayloadLiteralPrefixSenderState A
    (BankControl A strategy hwin)

private abbrev LeftReceiver :=
  ProfiledRawJointLeftFinitePayloadLiteralPrefixReceiverState A
    (BankControl A strategy hwin)

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

/-! ## Receiver-selected relay recurrence -/

/-- Within one strict-right block the receiver-selected full relay advances
once on the current physical input pair.  This is the equality hidden inside
the earlier rooted-pair preservation proof, exposed here because a final
homogeneous block has no later operational cut. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt_succ_of_right
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (hgraph : (env n).graph = .right) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt
        A strategy hwin initialTag env (n + 1) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayAdvance
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt
            A strategy hwin initialTag env n)
          ((env n).inputOne, (env n).inputTwo) := by
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin initialTag
  let pair :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
      A strategy hwin initialTag env n
  have hpending :=
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt_invariant
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
              profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
                  A strategy hwin initialTag env (n + 1) =
                ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvOne
                    A strategy hwin pair.1 (env n).inputOne).1,
                  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvTwo
                    A strategy hwin fallback pair.2 (env n).inputTwo pair.1
                      (env n).inputOne).1) := by
            rw [
              profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt,
              FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
              hgraph]
            rfl
          simp only [
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt,
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedOneAt,
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedTwoAt]
          rw [hnext, hone, htwo]
          rcases onePending with ⟨memberOne, sharedOne, payloadOne⟩
          rcases twoPending with ⟨memberTwo, sharedTwo, payloadTwo⟩
          cases memberOne <;> cases memberTwo <;> rfl

/-- Strict-left mirror. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt_succ_of_left
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (hgraph : (env n).graph = .left) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt
        A strategy hwin initialTag env (n + 1) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayAdvance
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt
            A strategy hwin initialTag env n)
          ((env n).inputOne, (env n).inputTwo) := by
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin initialTag
  let pair :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
      A strategy hwin initialTag env n
  have hpending :=
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt_invariant
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
              profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
                  A strategy hwin initialTag env (n + 1) =
                ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne
                    A strategy hwin fallback pair.1 (env n).inputOne pair.2
                      (env n).inputTwo).1,
                  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvTwo
                    A strategy hwin pair.2 (env n).inputTwo).1) := by
            rw [
              profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt,
              FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
              hgraph]
            rfl
          simp only [
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt,
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedOneAt,
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedTwoAt]
          rw [hnext, hone, htwo]
          rcases onePending with ⟨memberOne, sharedOne, payloadOne⟩
          rcases twoPending with ⟨memberTwo, sharedTwo, payloadTwo⟩
          cases memberOne <;> cases memberTwo <;> rfl

/-! ## Identification with the linked pair run -/

/-- Physical input pairs of a FullRestart suffix. -/
def profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartInputPairs
    (env : EnvironmentSequence In₁ In₂) : Nat → In₁ × In₂ :=
  fun n ↦ ((env n).inputOne, (env n).inputTwo)

/-- The actual Moore word of the repaired full-restart controller. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) :
    OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂) :=
  let controller :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartController
      A strategy hwin initialTag
  controller.globalMachine.globalMachineTraceWord controller.globalOutputOne
    controller.globalOutputTwo env

/-- On an all-right suffix, the right component of the receiver-selected
relay is literally the independently defined linked pair run. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt_eq_pairRun
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (hall : ∀ n : Nat, (env n).graph = .right) (n : Nat) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt
        A strategy hwin initialTag env n).1 =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairRun
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt
            A strategy hwin initialTag env 0).1.1
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt
            A strategy hwin initialTag env 0).1.2
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartInputPairs
            env) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt_succ_of_right
          A strategy hwin initialTag env n (hall n)]
      simp only [
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairRun,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayAdvance,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartInputPairs]
      rw [ih]

/-- All-left mirror. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt_eq_pairRun
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (hall : ∀ n : Nat, (env n).graph = .left) (n : Nat) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt
        A strategy hwin initialTag env n).2 =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairRun
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt
            A strategy hwin initialTag env 0).2.1
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt
            A strategy hwin initialTag env 0).2.2
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartInputPairs
            env) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt_succ_of_left
          A strategy hwin initialTag env n (hall n)]
      simp only [
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairRun,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayAdvance,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartInputPairs]
      rw [ih]

/-! ## Actual output on an arbitrary homogeneous suffix -/

/-- Once the blind sender is rooted at the receiver-selected right base, an
arbitrary homogeneous right suffix emits the corresponding linked pair run.
The semantic row is frozen at `.first`; the receiver's executable receive
bit is used only for restart detection. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartReferenceOutputAt_rightTail_add_eq_pairOutput
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (hnoBoth : ∀ m : Nat, (env m).graph ≠ .both)
    (start j : Nat)
    (hstart :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBlindBaseAt
          A strategy hwin initialTag env start).1.1 =
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt
          A strategy hwin initialTag env start).1.1)
    (hall : ∀ t : Nat, (env (start + t)).graph = .right) :
    let base :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt
        A strategy hwin initialTag env start
    let row : PairedEntryRow := .first
    let inputs : Nat → In₁ × In₂ := fun t ↦
      ((env (start + t)).inputOne, (env (start + t)).inputTwo)
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartReferenceOutputAt
        A strategy hwin initialTag env (start + j) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairOutput
        A strategy hwin base.1.1 base.1.2 row inputs j := by
  dsimp only
  have hrun :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightPairRun_eq_operational
      A strategy hwin initialTag env hnoBoth start j hstart
        (fun t _ ↦ hall t)
  obtain ⟨one, payloadOne, two, payloadTwo, hpair⟩ :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt_open_of_noBoth
      A strategy hwin initialTag env hnoBoth (start + j)
  have hselectedOne :
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedOneAt
          A strategy hwin initialTag env (start + j) = one := by
    simp [
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedOneAt,
      hpair]
  have hselectedTwo :
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedTwoAt
          A strategy hwin initialTag env (start + j) = two := by
    simp [
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedTwoAt,
      hpair]
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartReferenceOutputAt_eq_semantic]
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticOutputPairAt,
    hall j, hpair]
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairOutput,
    ← hrun]
  simp only [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvOne_open_output,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvTwo_open_output]
  simp only [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRetainedNoRecvOne,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvTwo,
    FiniteAcknowledgedDelayedCarrier.canonicalDeferredOpenRecvTwo,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOutputTwo,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartReceivedTwo,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRetainedRecvTwo,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne_open,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo_open,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBlindBaseAt,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt,
    hselectedOne, hselectedTwo]

/-- Left homogeneous-suffix mirror. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartReferenceOutputAt_leftTail_add_eq_pairOutput
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (hnoBoth : ∀ m : Nat, (env m).graph ≠ .both)
    (start j : Nat)
    (hstart :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBlindBaseAt
          A strategy hwin initialTag env start).2.1 =
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt
          A strategy hwin initialTag env start).2.1)
    (hall : ∀ t : Nat, (env (start + t)).graph = .left) :
    let base :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt
        A strategy hwin initialTag env start
    let row : PairedEntryRow := .first
    let inputs : Nat → In₁ × In₂ := fun t ↦
      ((env (start + t)).inputOne, (env (start + t)).inputTwo)
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartReferenceOutputAt
        A strategy hwin initialTag env (start + j) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairOutput
        A strategy hwin base.2.1 base.2.2 row inputs j := by
  dsimp only
  have hrun :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftPairRun_eq_operational
      A strategy hwin initialTag env hnoBoth start j hstart
        (fun t _ ↦ hall t)
  obtain ⟨one, payloadOne, two, payloadTwo, hpair⟩ :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt_open_of_noBoth
      A strategy hwin initialTag env hnoBoth (start + j)
  have hselectedOne :
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedOneAt
          A strategy hwin initialTag env (start + j) = one := by
    simp [
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedOneAt,
      hpair]
  have hselectedTwo :
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedTwoAt
          A strategy hwin initialTag env (start + j) = two := by
    simp [
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedTwoAt,
      hpair]
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartReferenceOutputAt_eq_semantic]
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticOutputPairAt,
    hall j, hpair]
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairOutput,
    ← hrun]
  simp only [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvTwo_open_output,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne_open_output]
  simp only [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRetainedNoRecvTwo,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne,
    FiniteAcknowledgedDelayedCarrier.canonicalDeferredOpenRecvOne,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOutputOne,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartReceivedOne,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRetainedRecvOne,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne_open,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo_open,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBlindBaseAt,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt,
    hselectedOne, hselectedTwo]

/-! ## The receive phase bit is stable on a homogeneous suffix -/

/-- If process two's local receive bit is set at the start of a right suffix,
it stays set throughout that suffix. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedTwoAt_rightTail_lastRecv
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (start : Nat)
    (hstart :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedTwoAt
        A strategy hwin initialTag env start).2.1 = true)
    (hall : ∀ t : Nat, (env (start + t)).graph = .right) : ∀ j : Nat,
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedTwoAt
      A strategy hwin initialTag env (start + j)).2.1 = true := by
  intro j
  cases j with
  | zero => simpa using hstart
  | succ j =>
      have hbits :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt_succ_selected_lastRecv
          A strategy hwin initialTag env (start + j)
      rw [hall j] at hbits
      have hbit :
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedTwoAt
            A strategy hwin initialTag env (start + j + 1)).2.1 = true := by
        simpa [
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedOneAt,
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedTwoAt]
          using hbits.2
      simpa [Nat.add_assoc] using hbit

/-- Process-one/all-left mirror. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedOneAt_leftTail_lastRecv
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (start : Nat)
    (hstart :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedOneAt
        A strategy hwin initialTag env start).2.1 = true)
    (hall : ∀ t : Nat, (env (start + t)).graph = .left) : ∀ j : Nat,
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedOneAt
      A strategy hwin initialTag env (start + j)).2.1 = true := by
  intro j
  cases j with
  | zero => simpa using hstart
  | succ j =>
      have hbits :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt_succ_selected_lastRecv
          A strategy hwin initialTag env (start + j)
      rw [hall j] at hbits
      have hbit :
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedOneAt
            A strategy hwin initialTag env (start + j + 1)).2.1 = true := by
        simpa [
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedOneAt,
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedTwoAt]
          using hbits.1
      simpa [Nat.add_assoc] using hbit

/-- Frozen-row form of the right-tail output theorem. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartReferenceOutputAt_rightTail_add_eq_pairOutput_first
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (hnoBoth : ∀ m : Nat, (env m).graph ≠ .both)
    (start : Nat)
    (hsender :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBlindBaseAt
          A strategy hwin initialTag env start).1.1 =
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt
          A strategy hwin initialTag env start).1.1)
    (hall : ∀ t : Nat, (env (start + t)).graph = .right) (j : Nat) :
    let base :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt
        A strategy hwin initialTag env start
    let inputs : Nat → In₁ × In₂ := fun t ↦
      ((env (start + t)).inputOne, (env (start + t)).inputTwo)
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartReferenceOutputAt
        A strategy hwin initialTag env (start + j) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairOutput
        A strategy hwin base.1.1 base.1.2 .first inputs j := by
  exact
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartReferenceOutputAt_rightTail_add_eq_pairOutput
      A strategy hwin initialTag env hnoBoth start j hsender hall

/-- Frozen-row left-tail mirror. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartReferenceOutputAt_leftTail_add_eq_pairOutput_first
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (hnoBoth : ∀ m : Nat, (env m).graph ≠ .both)
    (start : Nat)
    (hsender :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBlindBaseAt
          A strategy hwin initialTag env start).2.1 =
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt
          A strategy hwin initialTag env start).2.1)
    (hall : ∀ t : Nat, (env (start + t)).graph = .left) (j : Nat) :
    let base :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt
        A strategy hwin initialTag env start
    let inputs : Nat → In₁ × In₂ := fun t ↦
      ((env (start + t)).inputOne, (env (start + t)).inputTwo)
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartReferenceOutputAt
        A strategy hwin initialTag env (start + j) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairOutput
        A strategy hwin base.2.1 base.2.2 .first inputs j := by
  exact
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartReferenceOutputAt_leftTail_add_eq_pairOutput
      A strategy hwin initialTag env hnoBoth start j hsender hall

/-! ## Exact entry-state seam -/

/-- A represented right pair together with the DPA state equation that
`PairAtPrefix` itself deliberately does not contain.

This is the exact global-to-local seam for a fixed tail.  The semantic member
and the consumed literal prefix determine the accepted proof-side word; the
last field says that the actual checker has reached that word at the same
point.  Finite-prefix insensitivity cannot replace this equality because the
two runs may start in different DPA states.

Because the repaired controller keeps the semantic row at `.first`, this
package no longer crosses a row-change seam.  The predicates below retain an
existential represented occurrence only to connect the finite pair with the
actual checker state at the chosen cut. -/
structure
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairEntryStateAligned
    (root : BankControl A strategy hwin)
    (sender : RightSender A strategy hwin)
    (receiver : RightReceiver A strategy hwin)
    (row : PairedEntryRow) (inputs : Nat → In₁ × In₂)
    (actualWord : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (actualCut : Nat) : Type _ where
  family : ProfiledRawJointSemanticFamily A strategy (I := Unit)
  direction : ProfiledRawJointFamilyDirection
    (I := Unit) (In₁ := In₁) (In₂ := In₂)
  semanticMember : ProcOnePairedEntryRep strategy × A.State
  hmember : (family.semanticChild A direction).right () = some semanticMember
  anchor : Bool
  past : List (In₂ × In₁)
  sender_eq : sender =
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightSenderAtPrefix
      A strategy hwin root family direction semanticMember hmember past
  receiver_eq : receiver =
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightReceiverAtPrefix
      A strategy hwin root family direction semanticMember hmember anchor past
  state :
    let activation :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankRightActivations
        A strategy hwin family direction semanticMember hmember anchor
    let descriptor :=
      profiledRawJointRightFinitePayloadLinkedSiblingDescriptorOf A activation
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
          strategy hwin root)
    let tableEnv := OmegaWord.prependList past
      (fun k ↦ ((inputs k).2, (inputs k).1))
    A.run actualWord actualCut =
      A.runFrom (pairedCodeStateForRow A row descriptor.source.1.1)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPhysicalWord
          A strategy hwin root family direction semanticMember hmember anchor
            row tableEnv) past.length

/-- Left entry-state mirror. -/
structure
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairEntryStateAligned
    (root : BankControl A strategy hwin)
    (sender : LeftSender A strategy hwin)
    (receiver : LeftReceiver A strategy hwin)
    (row : PairedEntryRow) (inputs : Nat → In₁ × In₂)
    (actualWord : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (actualCut : Nat) : Type _ where
  family : ProfiledRawJointSemanticFamily A strategy (I := Unit)
  direction : ProfiledRawJointFamilyDirection
    (I := Unit) (In₁ := In₁) (In₂ := In₂)
  semanticMember : ProcTwoPairedEntryRep strategy × A.State
  hmember : (family.semanticChild A direction).left () = some semanticMember
  anchor : Bool
  past : List (In₁ × In₂)
  sender_eq : sender =
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftSenderAtPrefix
      A strategy hwin root family direction semanticMember hmember past
  receiver_eq : receiver =
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftReceiverAtPrefix
      A strategy hwin root family direction semanticMember hmember anchor past
  state :
    let activation :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftActivations
        A strategy hwin family direction semanticMember hmember anchor
    let descriptor :=
      profiledRawJointLeftFinitePayloadLinkedSiblingDescriptorOf A activation
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
          strategy hwin root)
    let tableEnv := OmegaWord.prependList past inputs
    A.run actualWord actualCut =
      A.runFrom (pairedCodeStateForRow A row descriptor.source.1.1)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPhysicalWord
          A strategy hwin root family direction semanticMember hmember anchor
            row tableEnv) past.length

namespace
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairEntryStateAligned

/-- Forgetting the checker equation recovers exactly `PairAtPrefix`. -/
theorem pairAtPrefix
    {root : BankControl A strategy hwin}
    {sender : RightSender A strategy hwin}
    {receiver : RightReceiver A strategy hwin}
    {row : PairedEntryRow} {inputs : Nat → In₁ × In₂}
    {actualWord : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂)}
    {actualCut : Nat}
    (aligned :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairEntryStateAligned
        A strategy hwin root sender receiver row inputs actualWord actualCut) :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairAtPrefix
      A strategy hwin root sender receiver := by
  exact ⟨aligned.family, aligned.direction, aligned.semanticMember,
    aligned.hmember, aligned.anchor, aligned.past, aligned.sender_eq,
    aligned.receiver_eq⟩

end
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairEntryStateAligned

namespace
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairEntryStateAligned

theorem pairAtPrefix
    {root : BankControl A strategy hwin}
    {sender : LeftSender A strategy hwin}
    {receiver : LeftReceiver A strategy hwin}
    {row : PairedEntryRow} {inputs : Nat → In₁ × In₂}
    {actualWord : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂)}
    {actualCut : Nat}
    (aligned :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairEntryStateAligned
        A strategy hwin root sender receiver row inputs actualWord actualCut) :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairAtPrefix
      A strategy hwin root sender receiver := by
  exact ⟨aligned.family, aligned.direction, aligned.semanticMember,
    aligned.hmember, aligned.anchor, aligned.past, aligned.sender_eq,
    aligned.receiver_eq⟩

end
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairEntryStateAligned

/-! ## Semantic entry alignment -/

/-- At one actual right-tail cut, the currently selected finite pair has a
represented semantic occurrence whose frozen `.first` state is the actual
DPA state. -/
def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightReanchoredEntryAt
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (cut : Nat) : Prop :=
  let base :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt
      A strategy hwin initialTag env cut
  let row : PairedEntryRow := .first
  let inputs : Nat → In₁ × In₂ := fun t ↦
    ((env (cut + t)).inputOne, (env (cut + t)).inputTwo)
  ∃ root : BankControl A strategy hwin,
    Nonempty
      (ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairEntryStateAligned
        A strategy hwin root base.1.1 base.1.2 row inputs
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord
            A strategy hwin initialTag env) cut)

/-- Left-cut mirror of semantic entry alignment. -/
def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftReanchoredEntryAt
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (cut : Nat) : Prop :=
  let base :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt
      A strategy hwin initialTag env cut
  let row : PairedEntryRow := .first
  let inputs : Nat → In₁ × In₂ := fun t ↦
    ((env (cut + t)).inputOne, (env (cut + t)).inputTwo)
  ∃ root : BankControl A strategy hwin,
    Nonempty
      (ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairEntryStateAligned
        A strategy hwin root base.2.1 base.2.2 row inputs
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord
            A strategy hwin initialTag env) cut)

/-- A positionwise form of right semantic entry alignment. -/
def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightDynamicallyReanchoredFrom
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (start : Nat) : Prop :=
  ∀ n : Nat,
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightReanchoredEntryAt
      A strategy hwin initialTag env (start + n)

/-- Left positionwise alignment mirror. -/
def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftDynamicallyReanchoredFrom
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (start : Nat) : Prop :=
  ∀ n : Nat,
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftReanchoredEntryAt
      A strategy hwin initialTag env (start + n)

/-! ## Consumption of the exact entry-state seam -/

/-- The named entry-state package is sufficient for an accepted actual
strict-right suffix.  Every other field is discharged from the operational
pair-run and the represented-table theorem. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_rightTail_acceptedOutputTailAligned
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (root : BankControl A strategy hwin) (start : Nat)
    (hnoBoth : ∀ m : Nat, (env m).graph ≠ .both)
    (hsender :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBlindBaseAt
          A strategy hwin initialTag env start).1.1 =
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt
          A strategy hwin initialTag env start).1.1)
    (hall : ∀ t : Nat, (env (start + t)).graph = .right)
    (entry :
      let base :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt
          A strategy hwin initialTag env start
      let inputs : Nat → In₁ × In₂ := fun t ↦
        ((env (start + t)).inputOne, (env (start + t)).inputTwo)
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairEntryStateAligned
        A strategy hwin root base.1.1 base.1.2 .first inputs
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord
            A strategy hwin initialTag env) start) :
    ∃ (source : A.State)
      (acceptedWord : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
      (acceptedCut : Nat),
      AcceptedOutputTailAligned A source acceptedWord
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord
          A strategy hwin initialTag env) acceptedCut start := by
  dsimp only at entry
  rcases entry with
    ⟨family, direction, semanticMember, hmember, anchor, past, hsenderAt,
      hreceiverAt, hstate⟩
  let activation :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRightActivations
      A strategy hwin family direction semanticMember hmember anchor
  let descriptor :=
    profiledRawJointRightFinitePayloadLinkedSiblingDescriptorOf A activation
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
        strategy hwin root)
  let inputs : Nat → In₁ × In₂ := fun t ↦
    ((env (start + t)).inputOne, (env (start + t)).inputTwo)
  let tableEnv : Nat → In₂ × In₁ := OmegaWord.prependList past
    (fun k ↦ ((inputs k).2, (inputs k).1))
  let acceptedWord :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPhysicalWord
      A strategy hwin root family direction semanticMember hmember anchor .first
        tableEnv
  let source := pairedCodeStateForRow A .first descriptor.source.1.1
  refine ⟨source, acceptedWord, past.length, ?_⟩
  refine
    { accepted := ?_
      state := ?_
      environment := ?_
      outputPair := ?_ }
  · exact
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPhysicalWord_acceptsFrom
        A strategy hwin root family direction semanticMember hmember anchor
          .first tableEnv
  · simpa [source, acceptedWord, descriptor, activation, tableEnv, inputs]
      using hstate
  · intro n
    have htrace :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartTraceWord_eq_referenceWord
        A strategy hwin initialTag env
    rw [profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord]
    rw [htrace]
    apply EnvironmentRound.eq_of_components
    · simp [acceptedWord, tableEnv, inputs,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPhysicalWord,
        pairedRightOmegaWord, OmegaWord.prependList_length_add,
        rightRoundRecord, RoundRecord.environment,
        FinitePairedPhysicalController.LiteralCrossGraphTraceInvariant.referenceWord]
    · simp [acceptedWord, tableEnv, inputs,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPhysicalWord,
        pairedRightOmegaWord, OmegaWord.prependList_length_add,
        rightRoundRecord, RoundRecord.environment,
        FinitePairedPhysicalController.LiteralCrossGraphTraceInvariant.referenceWord]
    · simp [acceptedWord, tableEnv, inputs,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPhysicalWord,
        pairedRightOmegaWord, OmegaWord.prependList_length_add,
        rightRoundRecord, RoundRecord.environment]
      simpa [
        FinitePairedPhysicalController.LiteralCrossGraphTraceInvariant.referenceWord]
        using hall n
  · intro n
    have hout :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartReferenceOutputAt_rightTail_add_eq_pairOutput_first
        A strategy hwin initialTag env hnoBoth start hsender hall n
    have hphysical :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairOutput_eq_physicalWord
        A strategy hwin root family direction semanticMember hmember anchor past
          .first inputs n
    dsimp only at hout
    rw [hsenderAt, hreceiverAt] at hout
    rw [hphysical] at hout
    have htrace :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartTraceWord_eq_referenceWord
        A strategy hwin initialTag env
    rw [profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord]
    rw [htrace]
    simpa [
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartReferenceOutputAt,
      acceptedWord, tableEnv, inputs] using hout

/-- Strict-left mirror of the complete accepted-tail handoff. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_leftTail_acceptedOutputTailAligned
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (root : BankControl A strategy hwin) (start : Nat)
    (hnoBoth : ∀ m : Nat, (env m).graph ≠ .both)
    (hsender :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBlindBaseAt
          A strategy hwin initialTag env start).2.1 =
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt
          A strategy hwin initialTag env start).2.1)
    (hall : ∀ t : Nat, (env (start + t)).graph = .left)
    (entry :
      let base :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt
          A strategy hwin initialTag env start
      let inputs : Nat → In₁ × In₂ := fun t ↦
        ((env (start + t)).inputOne, (env (start + t)).inputTwo)
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairEntryStateAligned
        A strategy hwin root base.2.1 base.2.2 .first inputs
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord
            A strategy hwin initialTag env) start) :
    ∃ (source : A.State)
      (acceptedWord : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
      (acceptedCut : Nat),
      AcceptedOutputTailAligned A source acceptedWord
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord
          A strategy hwin initialTag env) acceptedCut start := by
  dsimp only at entry
  rcases entry with
    ⟨family, direction, semanticMember, hmember, anchor, past, hsenderAt,
      hreceiverAt, hstate⟩
  let activation :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftActivations
      A strategy hwin family direction semanticMember hmember anchor
  let descriptor :=
    profiledRawJointLeftFinitePayloadLinkedSiblingDescriptorOf A activation
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
        strategy hwin root)
  let inputs : Nat → In₁ × In₂ := fun t ↦
    ((env (start + t)).inputOne, (env (start + t)).inputTwo)
  let tableEnv : Nat → In₁ × In₂ := OmegaWord.prependList past inputs
  let acceptedWord :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPhysicalWord
      A strategy hwin root family direction semanticMember hmember anchor .first
        tableEnv
  let source := pairedCodeStateForRow A .first descriptor.source.1.1
  refine ⟨source, acceptedWord, past.length, ?_⟩
  refine
    { accepted := ?_
      state := ?_
      environment := ?_
      outputPair := ?_ }
  · exact
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPhysicalWord_acceptsFrom
        A strategy hwin root family direction semanticMember hmember anchor
          .first tableEnv
  · simpa [source, acceptedWord, descriptor, activation, tableEnv, inputs]
      using hstate
  · intro n
    have htrace :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartTraceWord_eq_referenceWord
        A strategy hwin initialTag env
    rw [profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord]
    rw [htrace]
    apply EnvironmentRound.eq_of_components
    · simp [acceptedWord, tableEnv, inputs,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPhysicalWord,
        pairedLeftOmegaWord, OmegaWord.prependList_length_add,
        leftRoundRecord, RoundRecord.environment,
        FinitePairedPhysicalController.LiteralCrossGraphTraceInvariant.referenceWord]
    · simp [acceptedWord, tableEnv, inputs,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPhysicalWord,
        pairedLeftOmegaWord, OmegaWord.prependList_length_add,
        leftRoundRecord, RoundRecord.environment,
        FinitePairedPhysicalController.LiteralCrossGraphTraceInvariant.referenceWord]
    · simp [acceptedWord, tableEnv, inputs,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPhysicalWord,
        pairedLeftOmegaWord, OmegaWord.prependList_length_add,
        leftRoundRecord, RoundRecord.environment]
      simpa [
        FinitePairedPhysicalController.LiteralCrossGraphTraceInvariant.referenceWord]
        using hall n
  · intro n
    have hout :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartReferenceOutputAt_leftTail_add_eq_pairOutput_first
        A strategy hwin initialTag env hnoBoth start hsender hall n
    have hphysical :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairOutput_eq_physicalWord
        A strategy hwin root family direction semanticMember hmember anchor past
          .first inputs n
    dsimp only at hout
    rw [hsenderAt, hreceiverAt] at hout
    rw [hphysical] at hout
    have htrace :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartTraceWord_eq_referenceWord
        A strategy hwin initialTag env
    rw [profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord]
    rw [htrace]
    simpa [
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartReferenceOutputAt,
      acceptedWord, tableEnv, inputs] using hout

/-! ## The aligned socket closes homogeneous acceptance -/

/-- One represented occurrence at a frozen-row right cut closes
acceptance of the complete repaired-controller word. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord_accepts_of_rightReanchoredEntry
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (start : Nat)
    (hnoBoth : ∀ m : Nat, (env m).graph ≠ .both)
    (hsender :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBlindBaseAt
          A strategy hwin initialTag env start).1.1 =
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt
          A strategy hwin initialTag env start).1.1)
    (hall : ∀ t : Nat, (env (start + t)).graph = .right)
    (hreanchored :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightReanchoredEntryAt
        A strategy hwin initialTag env start) :
    A.Accepts
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord
        A strategy hwin initialTag env) := by
  dsimp only [
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightReanchoredEntryAt]
    at hreanchored
  rcases hreanchored with ⟨root, ⟨entry⟩⟩
  rcases
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_rightTail_acceptedOutputTailAligned
        A strategy hwin initialTag env root start hnoBoth hsender hall entry with
    ⟨source, acceptedWord, acceptedCut, aligned⟩
  exact aligned.accepts A

/-- One represented occurrence at a frozen-row left cut closes
the mirror word. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord_accepts_of_leftReanchoredEntry
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (start : Nat)
    (hnoBoth : ∀ m : Nat, (env m).graph ≠ .both)
    (hsender :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBlindBaseAt
          A strategy hwin initialTag env start).2.1 =
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt
          A strategy hwin initialTag env start).2.1)
    (hall : ∀ t : Nat, (env (start + t)).graph = .left)
    (hreanchored :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftReanchoredEntryAt
        A strategy hwin initialTag env start) :
    A.Accepts
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord
        A strategy hwin initialTag env) := by
  dsimp only [
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftReanchoredEntryAt]
    at hreanchored
  rcases hreanchored with ⟨root, ⟨entry⟩⟩
  rcases
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_leftTail_acceptedOutputTailAligned
        A strategy hwin initialTag env root start hnoBoth hsender hall entry with
    ⟨source, acceptedWord, acceptedCut, aligned⟩
  exact aligned.accepts A

/-- Positionwise alignment supplies the right cut consumed by acceptance. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord_accepts_of_rightDynamicReanchoring
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (start : Nat)
    (hnoBoth : ∀ m : Nat, (env m).graph ≠ .both)
    (hsender :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBlindBaseAt
          A strategy hwin initialTag env start).1.1 =
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt
          A strategy hwin initialTag env start).1.1)
    (hall : ∀ t : Nat, (env (start + t)).graph = .right)
    (hreanchored :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightDynamicallyReanchoredFrom
        A strategy hwin initialTag env start) :
    A.Accepts
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord
        A strategy hwin initialTag env) := by
  apply
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord_accepts_of_rightReanchoredEntry
      A strategy hwin initialTag env start hnoBoth hsender hall
  simpa [
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightDynamicallyReanchoredFrom]
    using hreanchored 0

/-- Left positionwise-alignment consumption mirror. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord_accepts_of_leftDynamicReanchoring
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (start : Nat)
    (hnoBoth : ∀ m : Nat, (env m).graph ≠ .both)
    (hsender :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBlindBaseAt
          A strategy hwin initialTag env start).2.1 =
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt
          A strategy hwin initialTag env start).2.1)
    (hall : ∀ t : Nat, (env (start + t)).graph = .left)
    (hreanchored :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftDynamicallyReanchoredFrom
        A strategy hwin initialTag env start) :
    A.Accepts
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord
        A strategy hwin initialTag env) := by
  apply
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord_accepts_of_leftReanchoredEntry
      A strategy hwin initialTag env start hnoBoth hsender hall
  simpa [
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftDynamicallyReanchoredFrom]
    using hreanchored 0

end

end DetParityAutomaton

end DistributedSynthesis
