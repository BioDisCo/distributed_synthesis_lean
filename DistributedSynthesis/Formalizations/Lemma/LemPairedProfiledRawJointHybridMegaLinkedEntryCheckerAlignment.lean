/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridMegaLinkedEntrySourceAlignment

/-!
# Checker alignment at linked strict-child creation

The source reconstructed by the full-restart tail is selected when the
preceding common root first enters a strict child.  This file identifies the
checker state at that creation boundary from two local facts:

* immediately before the handoff the checker is at the represented common
  `.both` source; and
* the physical handoff letter is the canonical strict child letter.

The common-root checker theorem advances the first fact through the second,
and executable-source alignment identifies the resulting tag source with the
source reconstructed by `FullRestart`.  A later simultaneous delivery still
requires the guarded finite-prefix scan/close theorem; it is deliberately not
collapsed into this one-step statement.
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

/-- A canonical strict-right creation advances the actual checker from the
represented common source to the exact executable source reconstructed by
the linked full-restart tail. -/
theorem profiledRawJointHybridMegaLinkedRightEntry_checker_of_record
    (control : ProfiledRawJointHybridCommonControl A strategy hwin)
    (input : In₁ × In₂)
    (tailEnv : EnvironmentSequence In₁ In₂)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (start : Nat)
    (hentry :
      let world :=
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A
          strategy hwin control).world
      A.run word start =
        pairedCodeStateForRow A .both (world.procOneSlot A).1.1)
    (hrecord :
      let state :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot A strategy
          hwin control
      let initial :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedCommonRootInitialOfState
          A strategy hwin state
      let next :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedStrictRightStep
          A strategy hwin initial input
      word start =
        rightRoundRecord (input.2, input.1) next.1.1 next.2.1) :
    let tag :=
      profiledRawJointHybridShadowPhaseLiveRightTag A strategy hwin control
        input
    let retained := tag.markedRetainedChildTag A strategy hwin
    A.run word (start + 1) =
      pairedCodeStateForRow A .first
        (profiledRawJointLeftFinitePayloadLiteralPrefixSenderSource
          A strategy hwin
            (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt
              A strategy hwin retained tailEnv 0).2.1 false).1.1 := by
  dsimp only at hentry hrecord ⊢
  let tag :=
    profiledRawJointHybridShadowPhaseLiveRightTag A strategy hwin control input
  have hstep :=
    profiledRawJointHybridMegaLinkedCommonRootstrictRight_checker_eq_tagSource
      A strategy hwin control input
  have hrun :
      A.run word (start + 1) =
        pairedCodeStateForRow A .first
          ((tag.initialLeftMove A strategy hwin).1.source).1.1 := by
    rw [A.run_succ, hentry, hrecord]
    simpa [tag] using hstep
  have hsource :=
    profiledRawJointHybridMegaLinkedRightEntry_senderSource_eq_tagSource A
      strategy hwin control input tailEnv
  rw [hrun]
  exact congrArg (fun source ↦ pairedCodeStateForRow A .first source.1.1)
    hsource.symm

/-- Strict-left / right-sender mirror. -/
theorem profiledRawJointHybridMegaLinkedLeftEntry_checker_of_record
    (control : ProfiledRawJointHybridCommonControl A strategy hwin)
    (input : In₁ × In₂)
    (tailEnv : EnvironmentSequence In₁ In₂)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (start : Nat)
    (hentry :
      let world :=
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A
          strategy hwin control).world
      A.run word start =
        pairedCodeStateForRow A .both (world.procTwoSlot A).1.1)
    (hrecord :
      let state :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot A strategy
          hwin control
      let initial :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedCommonRootInitialOfState
          A strategy hwin state
      let next :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedStrictLeftStep
          A strategy hwin initial input
      word start = leftRoundRecord input next.1.1 next.2.1) :
    let tag :=
      profiledRawJointHybridShadowPhaseLiveLeftTag A strategy hwin control input
    let retained := tag.markedRetainedChildTag A strategy hwin
    A.run word (start + 1) =
      pairedCodeStateForRow A .first
        (profiledRawJointRightFinitePayloadLiteralPrefixSenderSource
          A strategy hwin
            (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt
              A strategy hwin retained tailEnv 0).1.1 false).1.1 := by
  dsimp only at hentry hrecord ⊢
  let tag :=
    profiledRawJointHybridShadowPhaseLiveLeftTag A strategy hwin control input
  have hstep :=
    profiledRawJointHybridMegaLinkedCommonRootstrictLeft_checker_eq_tagSource
      A strategy hwin control input
  have hrun :
      A.run word (start + 1) =
        pairedCodeStateForRow A .first
          ((tag.initialRightMove A strategy hwin).1.source).1.1 := by
    rw [A.run_succ, hentry, hrecord]
    simpa [tag] using hstep
  have hsource :=
    profiledRawJointHybridMegaLinkedLeftEntry_senderSource_eq_tagSource A
      strategy hwin control input tailEnv
  rw [hrun]
  exact congrArg (fun source ↦ pairedCodeStateForRow A .first source.1.1)
    hsource.symm

end

end DetParityAutomaton

end DistributedSynthesis
