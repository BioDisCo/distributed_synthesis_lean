/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteDelayedBitResolver
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonDecoratedPolicyFreshnessCarrier
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCrossFreshStagedClose

/-!
# Concrete delayed candidates for the literal-cross carrier

This file instantiates the generic finite delayed fork with the two concrete
continuations present at a literal strict/simultaneous boundary:

* the open branch continues the finite literal mismatch table;
* the closed branch enters the checked fresh recurrent continuation.

Each candidate also carries the endpoint's finite decorated-policy freshness
state.  A right/`both` ambiguity is stored at process two and the left/`both`
mirror at process one.  The constructors below use the actual local literal
steps and the already checked fresh staged close; there is no semantic
pending control to reconstruct.

Resolution itself is inherited from `FiniteDelayedFork`: at the next receive
the delivered finite branch tag is read before the selected continuation's
receive output is evaluated.  In particular this module never assumes that
the open and closed receiver outputs are equal.
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

private abbrev FreshOne :=
  ProfiledRawJointGuardedCommonDecoratedFreshnessOneState A strategy hwin
    initial

private abbrev FreshTwo :=
  ProfiledRawJointGuardedCommonDecoratedFreshnessTwoState A strategy hwin
    initial

private abbrev MismatchOne :=
  ProfiledRawJointGuardedCommonLiteralCrossMismatchOneState A

private abbrev MismatchTwo :=
  ProfiledRawJointGuardedCommonLiteralCrossMismatchTwoState A

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

/-! ## One fixed finite candidate alphabet -/

/-- A process-one branch is either still in the literal table or has entered
the checked fresh recurrent bank.  Its freshness coordinate is retained in
both cases. -/
abbrev ProfiledRawJointGuardedCommonLiteralDelayedOneCandidate
    (initialBank : ProfiledRawJointInitialControllerBank A strategy) :=
  ProfiledRawJointGuardedCommonDecoratedFreshnessOneState A strategy hwin
      initial ×
    (ProfiledRawJointGuardedCommonLiteralCrossMismatchOneState A ⊕
      ProfiledRawJointGuardedHybridCombinedOneControl A strategy hwin
        initialBank
        (ProfiledRawJointGuardedCommonTailInitialOne A strategy hwin)
        (ProfiledRawJointGuardedCommonTailExceptionalOne A strategy hwin))

/-- Process-two mirror. -/
abbrev ProfiledRawJointGuardedCommonLiteralDelayedTwoCandidate
    (initialBank : ProfiledRawJointInitialControllerBank A strategy) :=
  ProfiledRawJointGuardedCommonDecoratedFreshnessTwoState A strategy hwin
      initial ×
    (ProfiledRawJointGuardedCommonLiteralCrossMismatchTwoState A ⊕
      ProfiledRawJointGuardedHybridCombinedTwoControl A strategy hwin
        initialBank
        (ProfiledRawJointGuardedCommonTailInitialTwo A strategy hwin)
        (ProfiledRawJointGuardedCommonTailExceptionalTwo A strategy hwin))

noncomputable instance
    profiledRawJointGuardedCommonLiteralDelayedOneCandidateFintype
    (initialBank : ProfiledRawJointInitialControllerBank A strategy) :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralDelayedOneCandidate A strategy hwin
        initialBank (initial := initial)) := by
  infer_instance

noncomputable instance
    profiledRawJointGuardedCommonLiteralDelayedTwoCandidateFintype
    (initialBank : ProfiledRawJointInitialControllerBank A strategy) :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralDelayedTwoCandidate A strategy hwin
        initialBank (initial := initial)) := by
  infer_instance

/-- Finite identity of one literal ambiguity occurrence.  The two endpoint
forks created by an actual simultaneous round use the same triple.  Repeated
occurrences with the same triple also have the same package-determined closed
continuation, so equality is the safe charged-shadow test used by the
symmetric product carrier. -/
abbrev ProfiledRawJointGuardedCommonLiteralDelayedForkId :=
  ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin initial
      (CrossValid A strategy hwin) ×
    (In₁ × In₂) × (In₁ × In₂)

noncomputable instance
    profiledRawJointGuardedCommonLiteralDelayedForkIdFintype :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralDelayedForkId A strategy hwin
        (initial := initial)) := by
  infer_instance

/-- The common finite identity installed in the two local forks at a
simultaneous boundary. -/
def successorLiteralDelayedForkId
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial (CrossValid A strategy hwin))
    (incoming blockInput : In₁ × In₂) :
    ProfiledRawJointGuardedCommonLiteralDelayedForkId A strategy hwin
      (initial := initial) :=
  (state, incoming, blockInput)

/-! ## Right/`both`: process two keeps the fork -/

/-- The two concrete process-two continuations at a right/`both` boundary.
The open control is the actual strict-right literal result; the closed control
is the already checked fresh staged continuation. -/
noncomputable def successorRightLiteralDelayedForkTwo
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial (CrossValid A strategy hwin))
    (incoming blockInput : In₁ × In₂) (anchor : Bool)
    (fresh : FreshTwo A strategy hwin (initial := initial)) :
    FiniteDelayedFork
      (ProfiledRawJointGuardedCommonLiteralDelayedTwoCandidate A strategy hwin
        initialBank (initial := initial)) :=
  let installed :=
    package.currentRightLiteralCrossMismatchInitial A strategy hwin
      (package.policy.successor state incoming) anchor
  let openStep :=
    profiledRawJointGuardedCommonLiteralCrossMismatchLocalStep A installed.1
      installed.2 blockInput .right
  let closed :=
    package.successorLiteralCrossFreshRightContinuation A strategy hwin
      initialBank state incoming blockInput
  ⟨(fresh, .inl openStep.2.2), (fresh, .inr closed.2)⟩

/-- The informed process-one strict-right branch. -/
noncomputable def successorRightLiteralDelayedOpenTaggedOne
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial (CrossValid A strategy hwin))
    (incoming blockInput : In₁ × In₂) (anchor : Bool)
    (fresh : FreshOne A strategy hwin (initial := initial))
    (initialBank : ProfiledRawJointInitialControllerBank A strategy) :
    FiniteDelayedTagged
      (ProfiledRawJointGuardedCommonLiteralDelayedOneCandidate A strategy hwin
        initialBank (initial := initial)) :=
  let installed :=
    package.currentRightLiteralCrossMismatchInitial A strategy hwin
      (package.policy.successor state incoming) anchor
  let openStep :=
    profiledRawJointGuardedCommonLiteralCrossMismatchLocalStep A installed.1
      installed.2 blockInput .right
  FiniteDelayedTagged.openBranch (fresh, .inl openStep.1.2)

/-- The informed process-one simultaneous-close branch. -/
noncomputable def successorRightLiteralDelayedClosedTaggedOne
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial (CrossValid A strategy hwin))
    (incoming blockInput : In₁ × In₂)
    (fresh : FreshOne A strategy hwin (initial := initial)) :
    FiniteDelayedTagged
      (ProfiledRawJointGuardedCommonLiteralDelayedOneCandidate A strategy hwin
        initialBank (initial := initial)) :=
  let closed :=
    package.successorLiteralCrossFreshRightContinuation A strategy hwin
      initialBank state incoming blockInput
  FiniteDelayedTagged.closedBranch (fresh, .inr closed.1)

/-! ## Left/`both`: process one keeps the fork -/

/-- Strict-left/simultaneous candidate fork at process one. -/
noncomputable def successorLeftLiteralDelayedForkOne
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial (CrossValid A strategy hwin))
    (incoming blockInput : In₁ × In₂) (anchor : Bool)
    (fresh : FreshOne A strategy hwin (initial := initial)) :
    FiniteDelayedFork
      (ProfiledRawJointGuardedCommonLiteralDelayedOneCandidate A strategy hwin
        initialBank (initial := initial)) :=
  let installed :=
    package.currentLeftLiteralCrossMismatchInitial A strategy hwin
      (package.policy.successor state incoming) anchor
  let openStep :=
    profiledRawJointGuardedCommonLiteralCrossMismatchLocalStep A installed.1
      installed.2 blockInput .left
  let closed :=
    package.successorLiteralCrossFreshRightContinuation A strategy hwin
      initialBank state incoming blockInput
  ⟨(fresh, .inl openStep.1.2), (fresh, .inr closed.1)⟩

/-- The informed process-two strict-left branch. -/
noncomputable def successorLeftLiteralDelayedOpenTaggedTwo
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial (CrossValid A strategy hwin))
    (incoming blockInput : In₁ × In₂) (anchor : Bool)
    (fresh : FreshTwo A strategy hwin (initial := initial)) :
    FiniteDelayedTagged
      (ProfiledRawJointGuardedCommonLiteralDelayedTwoCandidate A strategy hwin
        initialBank (initial := initial)) :=
  let installed :=
    package.currentLeftLiteralCrossMismatchInitial A strategy hwin
      (package.policy.successor state incoming) anchor
  let openStep :=
    profiledRawJointGuardedCommonLiteralCrossMismatchLocalStep A installed.1
      installed.2 blockInput .left
  FiniteDelayedTagged.openBranch (fresh, .inl openStep.2.2)

/-- The informed process-two simultaneous-close branch. -/
noncomputable def successorLeftLiteralDelayedClosedTaggedTwo
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial (CrossValid A strategy hwin))
    (incoming blockInput : In₁ × In₂)
    (fresh : FreshTwo A strategy hwin (initial := initial)) :
    FiniteDelayedTagged
      (ProfiledRawJointGuardedCommonLiteralDelayedTwoCandidate A strategy hwin
        initialBank (initial := initial)) :=
  let closed :=
    package.successorLiteralCrossFreshRightContinuation A strategy hwin
      initialBank state incoming blockInput
  FiniteDelayedTagged.closedBranch (fresh, .inr closed.2)

/-! ## Exact selection equations at the next receive -/

/-- On the strict-right history, process two selects the continued literal
control from its finite fork. -/
@[simp] theorem successorRightLiteralDelayedForkTwo_resolve_open
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial (CrossValid A strategy hwin))
    (incoming blockInput : In₁ × In₂) (anchor : Bool)
    (forkFresh : FreshTwo A strategy hwin (initial := initial))
    (tagFresh : FreshOne A strategy hwin (initial := initial)) :
    (package.successorRightLiteralDelayedForkTwo A strategy hwin initialBank
        state incoming blockInput anchor forkFresh).resolve
        (package.successorRightLiteralDelayedOpenTaggedOne A strategy hwin
          state incoming blockInput anchor tagFresh initialBank) =
      (forkFresh, .inl
        (profiledRawJointGuardedCommonLiteralCrossMismatchLocalStep A
          (package.currentRightLiteralCrossMismatchInitial A strategy hwin
            (package.policy.successor state incoming) anchor).1
          (package.currentRightLiteralCrossMismatchInitial A strategy hwin
            (package.policy.successor state incoming) anchor).2
          blockInput .right).2.2) := by
  rfl

/-- On the simultaneous history, process two selects the fresh recurrent
control.  Its output at the following receive may differ from the open
branch's output. -/
@[simp] theorem successorRightLiteralDelayedForkTwo_resolve_closed
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial (CrossValid A strategy hwin))
    (incoming blockInput : In₁ × In₂) (anchor : Bool)
    (forkFresh : FreshTwo A strategy hwin (initial := initial))
    (tagFresh : FreshOne A strategy hwin (initial := initial)) :
    (package.successorRightLiteralDelayedForkTwo A strategy hwin initialBank
        state incoming blockInput anchor forkFresh).resolve
        (package.successorRightLiteralDelayedClosedTaggedOne A strategy hwin
          initialBank state incoming blockInput tagFresh) =
      (forkFresh, .inr
        (package.successorLiteralCrossFreshRightContinuation A strategy hwin
          initialBank state incoming blockInput).2) := by
  rfl

/-- Strict-left mirror: process one selects its open literal continuation. -/
@[simp] theorem successorLeftLiteralDelayedForkOne_resolve_open
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial (CrossValid A strategy hwin))
    (incoming blockInput : In₁ × In₂) (anchor : Bool)
    (forkFresh : FreshOne A strategy hwin (initial := initial))
    (tagFresh : FreshTwo A strategy hwin (initial := initial)) :
    (package.successorLeftLiteralDelayedForkOne A strategy hwin initialBank
        state incoming blockInput anchor forkFresh).resolve
        (package.successorLeftLiteralDelayedOpenTaggedTwo A strategy hwin
          initialBank state incoming blockInput anchor tagFresh) =
      (forkFresh, .inl
        (profiledRawJointGuardedCommonLiteralCrossMismatchLocalStep A
          (package.currentLeftLiteralCrossMismatchInitial A strategy hwin
            (package.policy.successor state incoming) anchor).1
          (package.currentLeftLiteralCrossMismatchInitial A strategy hwin
            (package.policy.successor state incoming) anchor).2
          blockInput .left).1.2) := by
  rfl

/-- Simultaneous left mirror: process one selects the fresh recurrent
continuation. -/
@[simp] theorem successorLeftLiteralDelayedForkOne_resolve_closed
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial (CrossValid A strategy hwin))
    (incoming blockInput : In₁ × In₂) (anchor : Bool)
    (forkFresh : FreshOne A strategy hwin (initial := initial))
    (tagFresh : FreshTwo A strategy hwin (initial := initial)) :
    (package.successorLeftLiteralDelayedForkOne A strategy hwin initialBank
        state incoming blockInput anchor forkFresh).resolve
        (package.successorLeftLiteralDelayedClosedTaggedTwo A strategy hwin
          initialBank state incoming blockInput tagFresh) =
      (forkFresh, .inr
        (package.successorLiteralCrossFreshRightContinuation A strategy hwin
          initialBank state incoming blockInput).1) := by
  rfl

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
