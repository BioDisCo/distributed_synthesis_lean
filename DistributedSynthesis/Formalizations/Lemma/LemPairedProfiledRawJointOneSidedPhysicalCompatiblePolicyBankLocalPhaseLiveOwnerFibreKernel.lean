/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatiblePolicyBankLocalPhaseLiveOwnerFibreBlind
import DistributedSynthesis.Formalizations.Lemma.LemFinitePairedMealyControllerTrace

/-!
# Finite acknowledged owner-fibre recurrent kernel

This file installs the owner-fibre endpoint maps below the generic exact-close
acknowledgement relay.  From any certified bridge entry pair, the resulting
finite paired controller preserves both mutual semantic selection and blind
open/closed output coherence at every finite execution prefix.
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

private abbrev OneControl :=
  ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin

private abbrev TwoControl :=
  ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin

/-- The executable recurrent kernel.  Its transition maps inspect only the
endpoint's finite control, local input, and a delivered finite partner
control. -/
noncomputable def profiledRawJointRecurrentOwnerFibreBoundaryController
    (initialOne : OneControl A strategy hwin)
    (initialTwo : TwoControl A strategy hwin) :
    FinitePairedMealyController In₁ In₂ Out₁ Out₂ :=
  FiniteAcknowledgedDelayedCarrier.exactClosingPairedMealyController
    initialOne initialTwo
    (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin)
    (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin)
    (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy hwin)
    (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy hwin)
    (profiledRawJointRecurrentOwnerFibreBoundaryClose A strategy hwin)

/-- The complete output-aware invariant holds along every environment prefix
of the finite recurrent kernel. -/
theorem
    profiledRawJointRecurrentOwnerFibreBoundarySemanticControlTrace_invariant
    (initialOne : OneControl A strategy hwin)
    (initialTwo : TwoControl A strategy hwin)
    (hinitial :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOperational A strategy hwin
        initialOne initialTwo)
    (env : EnvironmentSequence In₁ In₂) : ∀ n : Nat,
    FiniteAcknowledgedDelayedCarrier.ExactClosingBlindForkInvariant
      (ProfiledRawJointRecurrentOwnerFibreBoundaryOperational A strategy hwin)
      (ProfiledRawJointRecurrentOwnerFibreBoundaryOneBlind A strategy hwin)
      (ProfiledRawJointRecurrentOwnerFibreBoundaryTwoBlind A strategy hwin)
      ((profiledRawJointRecurrentOwnerFibreBoundaryController A strategy hwin
        initialOne initialTwo).semanticControlTrace env n).1
      ((profiledRawJointRecurrentOwnerFibreBoundaryController A strategy hwin
        initialOne initialTwo).semanticControlTrace env n).2 := by
  let laws :=
    profiledRawJointRecurrentOwnerFibreBoundaryBlindForkLaws A strategy hwin
      initialOne initialTwo hinitial
  intro n
  induction n with
  | zero =>
      exact
        FiniteAcknowledgedDelayedCarrier.ExactClosingBlindForkLaws.initial_invariant
          initialOne initialTwo
          (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy
            hwin)
          (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy
            hwin)
          (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy
            hwin)
          (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy
            hwin)
          (profiledRawJointRecurrentOwnerFibreBoundaryClose A strategy hwin)
          (ProfiledRawJointRecurrentOwnerFibreBoundaryOperational A strategy
            hwin)
          (ProfiledRawJointRecurrentOwnerFibreBoundaryOneBlind A strategy hwin)
          (ProfiledRawJointRecurrentOwnerFibreBoundaryTwoBlind A strategy hwin)
          laws
  | succ n ih =>
      cases hgraph : (env n).graph with
      | right =>
          simpa only [FinitePairedMealyController.semanticControlTrace,
            FinitePairedMealyController.semanticAdvanceControls, hgraph,
            profiledRawJointRecurrentOwnerFibreBoundaryController,
            FiniteAcknowledgedDelayedCarrier.exactClosingPairedMealyController,
            FiniteAcknowledgedDelayedCarrier.pairedMealyController] using
            (FiniteAcknowledgedDelayedCarrier.ExactClosingBlindForkLaws.strictRight
              initialOne initialTwo
              (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy
                hwin)
              (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy
                hwin)
              (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A
                strategy hwin)
              (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A
                strategy hwin)
              (profiledRawJointRecurrentOwnerFibreBoundaryClose A strategy
                hwin)
              (ProfiledRawJointRecurrentOwnerFibreBoundaryOperational A
                strategy hwin)
              (ProfiledRawJointRecurrentOwnerFibreBoundaryOneBlind A strategy
                hwin)
              (ProfiledRawJointRecurrentOwnerFibreBoundaryTwoBlind A strategy
                hwin)
              laws
              ((profiledRawJointRecurrentOwnerFibreBoundaryController A
                strategy hwin initialOne initialTwo).semanticControlTrace env
                  n).1
              ((profiledRawJointRecurrentOwnerFibreBoundaryController A
                strategy hwin initialOne initialTwo).semanticControlTrace env
                  n).2
              (env n).inputOne (env n).inputTwo ih)
      | left =>
          simpa only [FinitePairedMealyController.semanticControlTrace,
            FinitePairedMealyController.semanticAdvanceControls, hgraph,
            profiledRawJointRecurrentOwnerFibreBoundaryController,
            FiniteAcknowledgedDelayedCarrier.exactClosingPairedMealyController,
            FiniteAcknowledgedDelayedCarrier.pairedMealyController] using
            (FiniteAcknowledgedDelayedCarrier.ExactClosingBlindForkLaws.strictLeft
              initialOne initialTwo
              (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy
                hwin)
              (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy
                hwin)
              (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A
                strategy hwin)
              (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A
                strategy hwin)
              (profiledRawJointRecurrentOwnerFibreBoundaryClose A strategy
                hwin)
              (ProfiledRawJointRecurrentOwnerFibreBoundaryOperational A
                strategy hwin)
              (ProfiledRawJointRecurrentOwnerFibreBoundaryOneBlind A strategy
                hwin)
              (ProfiledRawJointRecurrentOwnerFibreBoundaryTwoBlind A strategy
                hwin)
              laws
              ((profiledRawJointRecurrentOwnerFibreBoundaryController A
                strategy hwin initialOne initialTwo).semanticControlTrace env
                  n).1
              ((profiledRawJointRecurrentOwnerFibreBoundaryController A
                strategy hwin initialOne initialTwo).semanticControlTrace env
                  n).2
              (env n).inputOne (env n).inputTwo ih)
      | both =>
          simpa only [FinitePairedMealyController.semanticControlTrace,
            FinitePairedMealyController.semanticAdvanceControls, hgraph,
            profiledRawJointRecurrentOwnerFibreBoundaryController,
            FiniteAcknowledgedDelayedCarrier.exactClosingPairedMealyController,
            FiniteAcknowledgedDelayedCarrier.pairedMealyController] using
            (FiniteAcknowledgedDelayedCarrier.ExactClosingBlindForkLaws.both
              initialOne initialTwo
              (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy
                hwin)
              (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy
                hwin)
              (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A
                strategy hwin)
              (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A
                strategy hwin)
              (profiledRawJointRecurrentOwnerFibreBoundaryClose A strategy
                hwin)
              (ProfiledRawJointRecurrentOwnerFibreBoundaryOperational A
                strategy hwin)
              (ProfiledRawJointRecurrentOwnerFibreBoundaryOneBlind A strategy
                hwin)
              (ProfiledRawJointRecurrentOwnerFibreBoundaryTwoBlind A strategy
                hwin)
              laws
              ((profiledRawJointRecurrentOwnerFibreBoundaryController A
                strategy hwin initialOne initialTwo).semanticControlTrace env
                  n).1
              ((profiledRawJointRecurrentOwnerFibreBoundaryController A
                strategy hwin initialOne initialTwo).semanticControlTrace env
                  n).2
              (env n).inputOne (env n).inputTwo ih)

/-- At every finite prefix, the executable relay controls mutually select an
operational underlying pair, and every unresolved local fork has equal
no-receive output on its open and closed branches. -/
theorem
    profiledRawJointRecurrentOwnerFibreBoundarySemanticControlTrace_relayInvariant
    (initialOne : OneControl A strategy hwin)
    (initialTwo : TwoControl A strategy hwin)
    (hinitial :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOperational A strategy hwin
        initialOne initialTwo)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    FiniteAcknowledgedDelayedCarrier.ExactClosingRelayInvariant
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin)
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin)
      (ProfiledRawJointRecurrentOwnerFibreBoundaryOperational A strategy hwin)
      ((profiledRawJointRecurrentOwnerFibreBoundaryController A strategy hwin
        initialOne initialTwo).semanticControlTrace env n).1
      ((profiledRawJointRecurrentOwnerFibreBoundaryController A strategy hwin
        initialOne initialTwo).semanticControlTrace env n).2 := by
  apply
    FiniteAcknowledgedDelayedCarrier.ExactClosingBlindForkInvariant.toRelayInvariant
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin)
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin)
      (ProfiledRawJointRecurrentOwnerFibreBoundaryOperational A strategy hwin)
      (ProfiledRawJointRecurrentOwnerFibreBoundaryOneBlind A strategy hwin)
      (ProfiledRawJointRecurrentOwnerFibreBoundaryTwoBlind A strategy hwin)
      (profiledRawJointRecurrentOwnerFibreBoundaryBlindNoRecvLaws A strategy
        hwin)
  exact
    profiledRawJointRecurrentOwnerFibreBoundarySemanticControlTrace_invariant
      A strategy hwin initialOne initialTwo hinitial env n

end

end DetParityAutomaton

end DistributedSynthesis
