/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralDelayedBitResolver
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonTailCoreAdapter

/-!
# Local Mealy transitions on the literal delayed-candidate alphabet

The delayed candidate alphabet is the product of the finite freshness state
with either a retained literal-mismatch state or an existing recurrent
control.  This file gives it one total endpoint-local Mealy API:

* a mismatch constructor dispatches to the literal mismatch map;
* a recurrent constructor dispatches to the existing combined recurrent
  kernel; and
* the freshness coordinate advances by its corresponding honest local map.

The fixed `default` common root is used only by the recurrent kernel's
off-invariant receive totalization.  On every typed recurrent constructor
used by the delayed-bit construction, the indexed kernel dispatches directly
and the root is definitionally irrelevant.

No executable map below takes a graph, orientation, leader bit, strict-leader
bit, semantic history, or local view.
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

private abbrev CommonPoint :=
  ProfiledRawJointGuardedCommonSemanticPoint A strategy

private abbrev CrossValid :=
  ProfiledRawJointGuardedCommonLiteralCrossExtraValid A strategy hwin

namespace ProfiledRawJointGuardedCommonDecoratedPolicyPackage

variable {initial : CommonPoint A strategy}

private abbrev OneCandidate
    (initialBank : ProfiledRawJointInitialControllerBank A strategy) :=
  ProfiledRawJointGuardedCommonLiteralDelayedOneCandidate A strategy hwin
    initialBank (initial := initial)

private abbrev TwoCandidate
    (initialBank : ProfiledRawJointInitialControllerBank A strategy) :=
  ProfiledRawJointGuardedCommonLiteralDelayedTwoCandidate A strategy hwin
    initialBank (initial := initial)

/-- One fixed recurrent kernel used to totalize the candidate maps.  Its root
is consulted only in exceptional/off-invariant receive cases. -/
private noncomputable def literalDelayedCandidateKernel
    (initialBank : ProfiledRawJointInitialControllerBank A strategy) :=
  profiledRawJointGuardedCommonTailCoreKernel A strategy hwin initialBank
    default

/-! ## No-receive maps -/

/-- Process-one candidate non-receive, in state-first Mealy order. -/
noncomputable def literalDelayedCandidateNoRecvOne
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (state : OneCandidate A strategy hwin initialBank (initial := initial))
    (input : In₁) :
    OneCandidate A strategy hwin initialBank (initial := initial) × Out₁ :=
  let fresh := decoratedFreshnessNoRecvOne A strategy hwin state.1 input
  match state.2 with
  | .inl mismatch =>
      let next :=
        profiledRawJointGuardedCommonLiteralCrossMismatchNoRecvOne A mismatch
          input
      ((fresh, .inl next.2), next.1)
  | .inr recurrent =>
      let next :=
        (literalDelayedCandidateKernel A strategy hwin initialBank).noRecvOne
          recurrent input
      ((fresh, .inr next.2), next.1)

/-- Process-two mirror. -/
noncomputable def literalDelayedCandidateNoRecvTwo
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (state : TwoCandidate A strategy hwin initialBank (initial := initial))
    (input : In₂) :
    TwoCandidate A strategy hwin initialBank (initial := initial) × Out₂ :=
  let fresh := decoratedFreshnessNoRecvTwo A strategy hwin state.1 input
  match state.2 with
  | .inl mismatch =>
      let next :=
        profiledRawJointGuardedCommonLiteralCrossMismatchNoRecvTwo A mismatch
          input
      ((fresh, .inl next.2), next.1)
  | .inr recurrent =>
      let next :=
        (literalDelayedCandidateKernel A strategy hwin initialBank).noRecvTwo
          recurrent input
      ((fresh, .inr next.2), next.1)

@[simp] theorem literalDelayedCandidateNoRecvOne_mismatch
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (fresh :
      ProfiledRawJointGuardedCommonDecoratedFreshnessOneState A strategy hwin
        initial)
    (mismatch :
      ProfiledRawJointGuardedCommonLiteralCrossMismatchOneState A)
    (input : In₁) :
    literalDelayedCandidateNoRecvOne A strategy hwin initialBank
        (fresh, .inl mismatch) input =
      let next :=
        profiledRawJointGuardedCommonLiteralCrossMismatchNoRecvOne A mismatch
          input
      ((decoratedFreshnessNoRecvOne A strategy hwin fresh input,
          .inl next.2), next.1) := by
  rfl

@[simp] theorem literalDelayedCandidateNoRecvOne_recurrent
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (fresh :
      ProfiledRawJointGuardedCommonDecoratedFreshnessOneState A strategy hwin
        initial)
    (recurrent :
      ProfiledRawJointGuardedHybridCombinedOneControl A strategy hwin
        initialBank
        (ProfiledRawJointGuardedCommonTailInitialOne A strategy hwin)
        (ProfiledRawJointGuardedCommonTailExceptionalOne A strategy hwin))
    (input : In₁) :
    literalDelayedCandidateNoRecvOne A strategy hwin initialBank
        (fresh, .inr recurrent) input =
      let next :=
        (literalDelayedCandidateKernel A strategy hwin initialBank).noRecvOne
          recurrent input
      ((decoratedFreshnessNoRecvOne A strategy hwin fresh input,
          .inr next.2), next.1) := by
  rfl

@[simp] theorem literalDelayedCandidateNoRecvTwo_mismatch
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (fresh :
      ProfiledRawJointGuardedCommonDecoratedFreshnessTwoState A strategy hwin
        initial)
    (mismatch :
      ProfiledRawJointGuardedCommonLiteralCrossMismatchTwoState A)
    (input : In₂) :
    literalDelayedCandidateNoRecvTwo A strategy hwin initialBank
        (fresh, .inl mismatch) input =
      let next :=
        profiledRawJointGuardedCommonLiteralCrossMismatchNoRecvTwo A mismatch
          input
      ((decoratedFreshnessNoRecvTwo A strategy hwin fresh input,
          .inl next.2), next.1) := by
  rfl

@[simp] theorem literalDelayedCandidateNoRecvTwo_recurrent
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (fresh :
      ProfiledRawJointGuardedCommonDecoratedFreshnessTwoState A strategy hwin
        initial)
    (recurrent :
      ProfiledRawJointGuardedHybridCombinedTwoControl A strategy hwin
        initialBank
        (ProfiledRawJointGuardedCommonTailInitialTwo A strategy hwin)
        (ProfiledRawJointGuardedCommonTailExceptionalTwo A strategy hwin))
    (input : In₂) :
    literalDelayedCandidateNoRecvTwo A strategy hwin initialBank
        (fresh, .inr recurrent) input =
      let next :=
        (literalDelayedCandidateKernel A strategy hwin initialBank).noRecvTwo
          recurrent input
      ((decoratedFreshnessNoRecvTwo A strategy hwin fresh input,
          .inr next.2), next.1) := by
  rfl

/-! ## Receive maps -/

/-- Process-one candidate receive.  A literal state needs no delivered
control beyond the delivered input.  A recurrent/recurrent pair uses the
combined kernel; the mixed recurrent/literal case is totalized by the fixed
initial recurrent control and is outside the paired invariant. -/
noncomputable def literalDelayedCandidateRecvOne
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (one : OneCandidate A strategy hwin initialBank (initial := initial))
    (own : In₁)
    (two : TwoCandidate A strategy hwin initialBank (initial := initial))
    (delivered : In₂) :
    OneCandidate A strategy hwin initialBank (initial := initial) × Out₁ :=
  let fresh := decoratedFreshnessRecvOne A strategy hwin package one.1 own
    two.1 delivered
  match one.2, two.2 with
  | .inl mismatch, _ =>
      let next :=
        profiledRawJointGuardedCommonLiteralCrossMismatchRecvOne A mismatch own
          delivered
      ((fresh, .inl next.2), next.1)
  | .inr recurrentOne, .inr recurrentTwo =>
      let next :=
        (literalDelayedCandidateKernel A strategy hwin initialBank).recvOne
          recurrentOne own recurrentTwo delivered
      ((fresh, .inr next.2), next.1)
  | .inr recurrentOne, .inl _ =>
      let next :=
        (literalDelayedCandidateKernel A strategy hwin initialBank).recvOne
          recurrentOne own (.initial default) delivered
      ((fresh, .inr next.2), next.1)

/-- Process-two mirror. -/
noncomputable def literalDelayedCandidateRecvTwo
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (two : TwoCandidate A strategy hwin initialBank (initial := initial))
    (own : In₂)
    (one : OneCandidate A strategy hwin initialBank (initial := initial))
    (delivered : In₁) :
    TwoCandidate A strategy hwin initialBank (initial := initial) × Out₂ :=
  let fresh := decoratedFreshnessRecvTwo A strategy hwin package two.1 own
    one.1 delivered
  match two.2, one.2 with
  | .inl mismatch, _ =>
      let next :=
        profiledRawJointGuardedCommonLiteralCrossMismatchRecvTwo A mismatch own
          delivered
      ((fresh, .inl next.2), next.1)
  | .inr recurrentTwo, .inr recurrentOne =>
      let next :=
        (literalDelayedCandidateKernel A strategy hwin initialBank).recvTwo
          recurrentTwo own recurrentOne delivered
      ((fresh, .inr next.2), next.1)
  | .inr recurrentTwo, .inl _ =>
      let next :=
        (literalDelayedCandidateKernel A strategy hwin initialBank).recvTwo
          recurrentTwo own (.initial default) delivered
      ((fresh, .inr next.2), next.1)

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
