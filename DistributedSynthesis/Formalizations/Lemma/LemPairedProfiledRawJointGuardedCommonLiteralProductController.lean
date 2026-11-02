/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteAcknowledgedDelayedPairedMealyController
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralDelayedCandidateTransition
import DistributedSynthesis.Formalizations.Lemma.LemFinitePairedMealyControllerLiteralCrossTraceInvariant

/-!
# Concrete finite product controller for the literal-cross route

This file instantiates the acknowledged delayed carrier with the actual finite
candidate alphabets of the guarded literal construction.  A candidate stores
the leader-free decorated-policy freshness coordinate together with either a
literal mismatch control or an existing recurrent control.

At a receive, the acknowledgement carrier first selects both old candidates.
The endpoint-local transition then emits the selected candidate's physical
output and installs two next candidates:

* the open candidate is the ordinary strict receive continuation;
* the closed candidate is the checked fresh recurrent continuation at the
  current literal table.

The executable maps below take only local finite controls and the inputs
available at the endpoint.  They receive no graph, orientation, hierarchy
side, leader bit, strict-leader bit, semantic history, or view.
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

/-! ## Fixed finite endpoint alphabets -/

/-- Process-one candidate alphabet used by the acknowledged relay. -/
abbrev ProfiledRawJointGuardedCommonLiteralProductOneCandidate
    (initialBank : ProfiledRawJointInitialControllerBank A strategy) :=
  ProfiledRawJointGuardedCommonLiteralDelayedOneCandidate A strategy hwin
    initialBank (initial := initial)

/-- Process-two mirror. -/
abbrev ProfiledRawJointGuardedCommonLiteralProductTwoCandidate
    (initialBank : ProfiledRawJointInitialControllerBank A strategy) :=
  ProfiledRawJointGuardedCommonLiteralDelayedTwoCandidate A strategy hwin
    initialBank (initial := initial)

noncomputable instance literalProductOneCandidateFintype
    (initialBank : ProfiledRawJointInitialControllerBank A strategy) :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralProductOneCandidate A strategy hwin
        initialBank (initial := initial)) := by
  infer_instance

noncomputable instance literalProductTwoCandidateFintype
    (initialBank : ProfiledRawJointInitialControllerBank A strategy) :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralProductTwoCandidate A strategy hwin
        initialBank (initial := initial)) := by
  infer_instance

/-- Process-one acknowledged relay over the concrete candidate alphabet. -/
abbrev ProfiledRawJointGuardedCommonLiteralProductOneRelay
    (initialBank : ProfiledRawJointInitialControllerBank A strategy) :=
  FiniteAcknowledgedDelayedCarrier (Fin 5)
    (ProfiledRawJointGuardedCommonLiteralProductOneCandidate A strategy hwin
      initialBank (initial := initial))

/-- Process-two mirror. -/
abbrev ProfiledRawJointGuardedCommonLiteralProductTwoRelay
    (initialBank : ProfiledRawJointInitialControllerBank A strategy) :=
  FiniteAcknowledgedDelayedCarrier (Fin 5)
    (ProfiledRawJointGuardedCommonLiteralProductTwoCandidate A strategy hwin
      initialBank (initial := initial))

noncomputable instance literalProductOneRelayFintype
    (initialBank : ProfiledRawJointInitialControllerBank A strategy) :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralProductOneRelay A strategy hwin
        initialBank (initial := initial)) := by
  infer_instance

noncomputable instance literalProductTwoRelayFintype
    (initialBank : ProfiledRawJointInitialControllerBank A strategy) :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralProductTwoRelay A strategy hwin
        initialBank (initial := initial)) := by
  infer_instance

/-! ## Endpoint-facing fresh recurrent continuation -/

private abbrev RecurrentOne
    (initialBank : ProfiledRawJointInitialControllerBank A strategy) :=
  ProfiledRawJointGuardedHybridCombinedOneControl A strategy hwin initialBank
    (ProfiledRawJointGuardedCommonTailInitialOne A strategy hwin)
    (ProfiledRawJointGuardedCommonTailExceptionalOne A strategy hwin)

private abbrev RecurrentTwo
    (initialBank : ProfiledRawJointInitialControllerBank A strategy) :=
  ProfiledRawJointGuardedHybridCombinedTwoControl A strategy hwin initialBank
    (ProfiledRawJointGuardedCommonTailInitialTwo A strategy hwin)
    (ProfiledRawJointGuardedCommonTailExceptionalTwo A strategy hwin)

/-- Recurrent controls obtained by closing the literal table stored at an
already current finite policy state.  This is the endpoint-facing form of the
existing predecessor-facing `successorLiteralCrossFreshRightContinuation`. -/
noncomputable def literalCrossFreshRightContinuationAt
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (current : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy
      hwin initial (CrossValid A strategy hwin))
    (blockInput : In₁ × In₂) :
    RecurrentOne A strategy hwin initialBank ×
      RecurrentTwo A strategy hwin initialBank :=
  let close := package.literalCrossFreshRightStagedCloseAt A strategy hwin
    current blockInput
  let key := profiledRawJointGuardedCommonRightStagedCombinedKey A strategy
    hwin initialBank close
  (.leftReceiver key
      (profiledRawJointGuardedCommonRightStagedInitialLeftReceiver A strategy
        hwin initialBank close),
    .leftOwner key
      (profiledRawJointGuardedCommonRightStagedInitialLeftOwner A strategy hwin
        initialBank close))

/-- The endpoint-facing wrapper is definitionally the already checked
successor continuation when the current state is displayed as a policy
successor. -/
@[simp] theorem literalCrossFreshRightContinuationAt_successor
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial (CrossValid A strategy hwin))
    (incoming blockInput : In₁ × In₂) :
    package.literalCrossFreshRightContinuationAt A strategy hwin initialBank
        (package.policy.successor state incoming) blockInput =
      package.successorLiteralCrossFreshRightContinuation A strategy hwin
        initialBank state incoming blockInput := by
  rfl

/-! ## Exact initial candidates -/

/-- Both endpoints start from the root decorated policy state and the same
retained right literal table.  `false` is a fixed finite table member, not an
observed graph or leader bit. -/
noncomputable def literalProductInitialCandidates
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin)) :
    ProfiledRawJointGuardedCommonLiteralProductOneCandidate A strategy hwin
        initialBank (initial := initial) ×
      ProfiledRawJointGuardedCommonLiteralProductTwoCandidate A strategy hwin
        initialBank (initial := initial) :=
  let current := package.policy.run []
  let fresh := decoratedFreshnessBothInitial A strategy hwin current
  let mismatch := package.currentRightLiteralCrossMismatchInitial A strategy
    hwin current false
  ((fresh.1, .inl mismatch.1), (fresh.2, .inl mismatch.2))

@[simp] theorem literalProductInitialCandidates_freshness
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin)) :
    ((package.literalProductInitialCandidates A strategy hwin
          initialBank).1.1,
      (package.literalProductInitialCandidates A strategy hwin
          initialBank).2.1) =
      decoratedFreshnessBothInitial A strategy hwin (package.policy.run []) :=
  rfl

@[simp] theorem literalProductInitialCandidates_mismatch
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin)) :
    ((package.literalProductInitialCandidates A strategy hwin
          initialBank).1.2,
      (package.literalProductInitialCandidates A strategy hwin
          initialBank).2.2) =
      (.inl
          (package.currentRightLiteralCrossMismatchInitial A strategy hwin
            (package.policy.run []) false).1,
        .inl
          (package.currentRightLiteralCrossMismatchInitial A strategy hwin
            (package.policy.run []) false).2) :=
  rfl

/-! ## Local receive forks -/

/-- Process-one receive transition after the acknowledgement carrier has
selected both old candidates.  The output belongs to the selected current
transition; only the next control is forked between strict and simultaneous
interpretations. -/
noncomputable def literalProductRecvForkOne
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (one : ProfiledRawJointGuardedCommonLiteralProductOneCandidate A strategy
      hwin initialBank (initial := initial))
    (own : In₁)
    (two : ProfiledRawJointGuardedCommonLiteralProductTwoCandidate A strategy
      hwin initialBank (initial := initial))
    (delivered : In₂) :
    FiniteDelayedFork
        (ProfiledRawJointGuardedCommonLiteralProductOneCandidate A strategy
          hwin initialBank (initial := initial)) × Out₁ :=
  let openResult := package.literalDelayedCandidateRecvOne A strategy hwin
    initialBank one own two delivered
  let current := decoratedFreshnessCurrent A strategy hwin one.1 two.1
  let closed := package.literalCrossFreshRightContinuationAt A strategy hwin
    initialBank current (own, delivered)
  (⟨openResult.1, (openResult.1.1, .inr closed.1)⟩, openResult.2)

/-- Process-two mirror. -/
noncomputable def literalProductRecvForkTwo
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (two : ProfiledRawJointGuardedCommonLiteralProductTwoCandidate A strategy
      hwin initialBank (initial := initial))
    (own : In₂)
    (one : ProfiledRawJointGuardedCommonLiteralProductOneCandidate A strategy
      hwin initialBank (initial := initial))
    (delivered : In₁) :
    FiniteDelayedFork
        (ProfiledRawJointGuardedCommonLiteralProductTwoCandidate A strategy
          hwin initialBank (initial := initial)) × Out₂ :=
  let openResult := package.literalDelayedCandidateRecvTwo A strategy hwin
    initialBank two own one delivered
  let current := decoratedFreshnessCurrent A strategy hwin one.1 two.1
  let closed := package.literalCrossFreshRightContinuationAt A strategy hwin
    initialBank current (delivered, own)
  (⟨openResult.1, (openResult.1.1, .inr closed.2)⟩, openResult.2)

@[simp] theorem literalProductRecvForkOne_open
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (one : ProfiledRawJointGuardedCommonLiteralProductOneCandidate A strategy
      hwin initialBank (initial := initial))
    (own : In₁)
    (two : ProfiledRawJointGuardedCommonLiteralProductTwoCandidate A strategy
      hwin initialBank (initial := initial))
    (delivered : In₂) :
    (package.literalProductRecvForkOne A strategy hwin initialBank one own two
      delivered).1.openControl =
      (package.literalDelayedCandidateRecvOne A strategy hwin initialBank one
        own two delivered).1 :=
  rfl

@[simp] theorem literalProductRecvForkOne_closed
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (one : ProfiledRawJointGuardedCommonLiteralProductOneCandidate A strategy
      hwin initialBank (initial := initial))
    (own : In₁)
    (two : ProfiledRawJointGuardedCommonLiteralProductTwoCandidate A strategy
      hwin initialBank (initial := initial))
    (delivered : In₂) :
    (package.literalProductRecvForkOne A strategy hwin initialBank one own two
      delivered).1.closedControl =
      ((package.literalDelayedCandidateRecvOne A strategy hwin initialBank one
          own two delivered).1.1,
        .inr
          (package.literalCrossFreshRightContinuationAt A strategy hwin
            initialBank
              (decoratedFreshnessCurrent A strategy hwin one.1 two.1)
              (own, delivered)).1) :=
  rfl

@[simp] theorem literalProductRecvForkTwo_open
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (two : ProfiledRawJointGuardedCommonLiteralProductTwoCandidate A strategy
      hwin initialBank (initial := initial))
    (own : In₂)
    (one : ProfiledRawJointGuardedCommonLiteralProductOneCandidate A strategy
      hwin initialBank (initial := initial))
    (delivered : In₁) :
    (package.literalProductRecvForkTwo A strategy hwin initialBank two own one
      delivered).1.openControl =
      (package.literalDelayedCandidateRecvTwo A strategy hwin initialBank two
        own one delivered).1 :=
  rfl

@[simp] theorem literalProductRecvForkTwo_closed
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (two : ProfiledRawJointGuardedCommonLiteralProductTwoCandidate A strategy
      hwin initialBank (initial := initial))
    (own : In₂)
    (one : ProfiledRawJointGuardedCommonLiteralProductOneCandidate A strategy
      hwin initialBank (initial := initial))
    (delivered : In₁) :
    (package.literalProductRecvForkTwo A strategy hwin initialBank two own one
      delivered).1.closedControl =
      ((package.literalDelayedCandidateRecvTwo A strategy hwin initialBank two
          own one delivered).1.1,
        .inr
          (package.literalCrossFreshRightContinuationAt A strategy hwin
            initialBank
              (decoratedFreshnessCurrent A strategy hwin one.1 two.1)
              (delivered, own)).2) :=
  rfl

/-! ## The concrete paired Mealy and physical controllers -/

/-- Fully finite paired Mealy controller for one winning strategy and one
selected decorated common-policy package. -/
noncomputable def literalProductMealyController
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin)) :
    FinitePairedMealyController In₁ In₂ Out₁ Out₂ :=
  FiniteAcknowledgedDelayedCarrier.pairedMealyController
    (package.literalProductInitialCandidates A strategy hwin initialBank).1
    (package.literalProductInitialCandidates A strategy hwin initialBank).2
    (literalDelayedCandidateNoRecvOne A strategy hwin initialBank)
    (literalDelayedCandidateNoRecvTwo A strategy hwin initialBank)
    (package.literalProductRecvForkOne A strategy hwin initialBank)
    (package.literalProductRecvForkTwo A strategy hwin initialBank)

/-- Moore physical controller consumed by the direct readback endpoint. -/
noncomputable def literalProductPhysicalController
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin)) :
    FinitePairedPhysicalController In₁ In₂ Out₁ Out₂ :=
  (package.literalProductMealyController A strategy hwin initialBank).mooreize

/-! ## Proof-side reachable core -/

/-- The pair of actual candidate controls selected mutually by the two
delivered acknowledgement relays.  This is a proof-side projection; the
executable receive maps perform the same two selections internally. -/
def literalProductResolvedCandidates
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (one : ProfiledRawJointGuardedCommonLiteralProductOneRelay A strategy hwin
      initialBank (initial := initial))
    (two : ProfiledRawJointGuardedCommonLiteralProductTwoRelay A strategy hwin
      initialBank (initial := initial)) :
    ProfiledRawJointGuardedCommonLiteralProductOneCandidate A strategy hwin
        initialBank (initial := initial) ×
      ProfiledRawJointGuardedCommonLiteralProductTwoCandidate A strategy hwin
        initialBank (initial := initial) :=
  (FiniteAcknowledgedDelayedCarrier.resolvedControl one two,
    FiniteAcknowledgedDelayedCarrier.resolvedControl two one)

/-- Every unresolved process-one fork must emit one common nonreceive output
for all next local inputs.  This is the exact operational condition under
which the relay's branchwise no-receive update is sound. -/
def LiteralProductNoRecvOneCoherent
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (one : ProfiledRawJointGuardedCommonLiteralProductOneRelay A strategy hwin
      initialBank (initial := initial)) : Prop :=
  match one.current with
  | .known _ => True
  | .fork _ candidates => ∀ input : In₁,
      candidates.NoRecvMealyOutputCoherent
        (literalDelayedCandidateNoRecvOne A strategy hwin initialBank) input

/-- Process-two mirror. -/
def LiteralProductNoRecvTwoCoherent
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (two : ProfiledRawJointGuardedCommonLiteralProductTwoRelay A strategy hwin
      initialBank (initial := initial)) : Prop :=
  match two.current with
  | .known _ => True
  | .fork _ candidates => ∀ input : In₂,
      candidates.NoRecvMealyOutputCoherent
        (literalDelayedCandidateNoRecvTwo A strategy hwin initialBank) input

/-- Minimal concrete invariant common to all graph regimes.

The selected actual candidates carry a leader-free aligned fresh policy copy,
that copy is reachable in the fixed decorated rational policy, and every
unresolved no-receive fork is output-coherent.  The acknowledgement layer's
`Selects` invariant and the semantic literal/recurrent row invariant extend
this core in the final trace proof; neither is executable state. -/
structure LiteralProductCoreInvariant
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (relays :
      ProfiledRawJointGuardedCommonLiteralProductOneRelay A strategy hwin
          initialBank (initial := initial) ×
        ProfiledRawJointGuardedCommonLiteralProductTwoRelay A strategy hwin
          initialBank (initial := initial)) : Prop where
  freshnessAligned :
    let selected := literalProductResolvedCandidates A strategy hwin
      initialBank relays.1 relays.2
    DecoratedFreshnessAligned A strategy hwin selected.1.1 selected.2.1
  currentReachable :
    let selected := literalProductResolvedCandidates A strategy hwin
      initialBank relays.1 relays.2
    ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
      initial (CrossValid A strategy hwin) package.policy
        (decoratedFreshnessCurrent A strategy hwin selected.1.1 selected.2.1)
  noRecvOneCoherent :
    LiteralProductNoRecvOneCoherent A strategy hwin initialBank relays.1
  noRecvTwoCoherent :
    LiteralProductNoRecvTwoCoherent A strategy hwin initialBank relays.2

/-- The concrete controller starts in the reachable aligned core with no
unresolved fork and hence vacuous no-receive coherence obligations. -/
theorem literalProductMealyController_initial_coreInvariant
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin)) :
    LiteralProductCoreInvariant A strategy hwin initialBank package
      ((package.literalProductMealyController A strategy hwin
          initialBank).initialOne,
        (package.literalProductMealyController A strategy hwin
          initialBank).initialTwo) := by
  constructor
  · exact decoratedFreshnessBothInitial_aligned A strategy hwin
      (package.policy.run [])
  · exact package.initial_reachable A strategy hwin
  · trivial
  · trivial

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
