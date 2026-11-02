/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankLinkedDeferredMemberController
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankLinkedLiveLane
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorInstalledOutputTail

/-!
# Fixed output tails of one live linked-bank occurrence

This file isolates the controller-local part of eventual homogeneous-tail
bookkeeping.  Once a linked sender/receiver pair is known to represent one
literal occurrence at an arbitrary finite prefix, continued one-way rounds
stay on that occurrence and emit exactly a suffix of its ordinary physical
sibling word.  The finite prefix and its omega completion are proof-side.

The remaining outer-controller obligation is only to locate such a live pair
after the final switch and to identify the DPA state at that cut.  No local
transition receives a graph direction, hierarchy side, leader bit, history,
or semantic witness.
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

/-! ## Pure one-way runs of one linked pair -/

/-- The two linked right-table controls before suffix round `n`. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairRun
    (sender : RightSender A strategy hwin)
    (receiver : RightReceiver A strategy hwin)
    (inputs : Nat → In₁ × In₂) : Nat →
      RightSender A strategy hwin × RightReceiver A strategy hwin
  | 0 => (sender, receiver)
  | n + 1 =>
      let prior :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairRun
          sender receiver inputs n
      ((profiledRawJointRightFinitePayloadLiteralPrefixSenderNoRecv A prior.1
          (inputs n).1).2,
        (profiledRawJointRightFinitePayloadLiteralPrefixReceiverRecv A prior.2
          (inputs n).2 (inputs n).1).2)

/-- Output pair emitted by that right-table pair in suffix round `n`. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairOutput
    (sender : RightSender A strategy hwin)
    (receiver : RightReceiver A strategy hwin)
    (row : PairedEntryRow) (inputs : Nat → In₁ × In₂)
    (n : Nat) : Out₁ × Out₂ :=
  let prior :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairRun
      A strategy hwin sender receiver inputs n
  ((profiledRawJointRightFinitePayloadLiteralPrefixSenderNoRecv A prior.1
      (inputs n).1).1,
    pairedRightInformedForRow row
      (profiledRawJointRightFinitePayloadLiteralPrefixReceiverRecv A prior.2
        (inputs n).2 (inputs n).1).1.physical)

/-- Left-table mirror. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairRun
    (sender : LeftSender A strategy hwin)
    (receiver : LeftReceiver A strategy hwin)
    (inputs : Nat → In₁ × In₂) : Nat →
      LeftSender A strategy hwin × LeftReceiver A strategy hwin
  | 0 => (sender, receiver)
  | n + 1 =>
      let prior :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairRun
          sender receiver inputs n
      ((profiledRawJointLeftFinitePayloadLiteralPrefixSenderNoRecv A prior.1
          (inputs n).2).2,
        (profiledRawJointLeftFinitePayloadLiteralPrefixReceiverRecv A prior.2
          (inputs n).1 (inputs n).2).2)

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairOutput
    (sender : LeftSender A strategy hwin)
    (receiver : LeftReceiver A strategy hwin)
    (row : PairedEntryRow) (inputs : Nat → In₁ × In₂)
    (n : Nat) : Out₁ × Out₂ :=
  let prior :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairRun
      A strategy hwin sender receiver inputs n
  (pairedLeftInformedForRow row
      (profiledRawJointLeftFinitePayloadLiteralPrefixReceiverRecv A prior.2
        (inputs n).1 (inputs n).2).1.physical,
    (profiledRawJointLeftFinitePayloadLiteralPrefixSenderNoRecv A prior.1
      (inputs n).2).1)

end

end DetParityAutomaton

end DistributedSynthesis
