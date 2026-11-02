/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCombinedFreshPendingOnly
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCombinedFreshPendingOnlyPolicyAcceptance

/-!
# A concrete root for the pending-only literal-table controller

The table-only construction is parametrized by two initial pending controls.
This file removes that last piece of controller plumbing.  Both endpoints are
started with the root copy of the one decorated policy, opposite tables at one
fixed finite key, the same fixed member, and an empty stage payload.

The initial table key affects only a finite prefix.  After the first receive,
the already proved fresh handlers replace it by the literal child selected by
the actual policy edge.  The two freshness coordinates, on the other hand,
are exactly the root coordinates from the start; this is the coordinate used
by the accepted policy-path theorem.

No executable map below receives a graph, orientation, hierarchy side,
leader bit, strict-leader bit, history, or semantic view.
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

private abbrev Package :=
  ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy hwin initial
    (CrossValid A strategy hwin)

private abbrev Key (package : Package A strategy hwin (initial := initial)) :=
  ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin package

private abbrev OneShared
    (package : Package A strategy hwin (initial := initial)) :=
  ProfiledRawJointGuardedCommonLiteralCombinedFreshOneShared A strategy hwin
    package

private abbrev TwoShared
    (package : Package A strategy hwin (initial := initial)) :=
  ProfiledRawJointGuardedCommonLiteralCombinedFreshTwoShared A strategy hwin
    package

private abbrev OnePending
    (package : Package A strategy hwin (initial := initial)) :=
  FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
    (OneShared A strategy hwin package)
    (ProfiledRawJointGuardedCommonLiteralCombinedFreshOnePayload A strategy
      hwin package)

private abbrev TwoPending
    (package : Package A strategy hwin (initial := initial)) :=
  FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
    (TwoShared A strategy hwin package)
    (ProfiledRawJointGuardedCommonLiteralCombinedFreshTwoPayload A strategy
      hwin package)

/-! ## One fully concrete initial pair -/

/-- A harmless finite table key used before the first actual receive. -/
def literalCombinedFreshPendingOnlyInitialKey
    (package : Package A strategy hwin (initial := initial)) :
    Key A strategy hwin package :=
  (package.policy.run [], (default, default))

/-- Process one's root shared value. -/
noncomputable def literalCombinedFreshPendingOnlyInitialOneShared
    (package : Package A strategy hwin (initial := initial)) :
    OneShared A strategy hwin package :=
  let fresh := decoratedFreshnessBothInitial A strategy hwin
    (package.policy.run [])
  let key := package.literalCombinedFreshPendingOnlyInitialKey A strategy hwin
  (fresh.1,
    package.literalLeftSeamStagedSenderInitial A strategy hwin key,
    ⟨package.literalRightSeamStagedReceiverInitial A strategy hwin key
        .both false,
      package.literalRightSeamStagedReceiverInitial A strategy hwin key .both
        true⟩)

/-- Process-two mirror at the same key and the mirror root freshness copy. -/
noncomputable def literalCombinedFreshPendingOnlyInitialTwoShared
    (package : Package A strategy hwin (initial := initial)) :
    TwoShared A strategy hwin package :=
  let fresh := decoratedFreshnessBothInitial A strategy hwin
    (package.policy.run [])
  let key := package.literalCombinedFreshPendingOnlyInitialKey A strategy hwin
  (fresh.2,
    package.literalRightSeamStagedSenderInitial A strategy hwin key,
    ⟨package.literalLeftSeamStagedReceiverInitial A strategy hwin key
        .both false,
      package.literalLeftSeamStagedReceiverInitial A strategy hwin key .both
        true⟩)

/-- The fixed initial member is proof-side table member `false`; it is not a
graph or leader observation. -/
noncomputable def literalCombinedFreshPendingOnlyInitialOne
    (package : Package A strategy hwin (initial := initial)) :
    OnePending A strategy hwin package :=
  (false,
    package.literalCombinedFreshPendingOnlyInitialOneShared A strategy hwin,
    none)

/-- Process-two mirror. -/
noncomputable def literalCombinedFreshPendingOnlyInitialTwo
    (package : Package A strategy hwin (initial := initial)) :
    TwoPending A strategy hwin package :=
  (false,
    package.literalCombinedFreshPendingOnlyInitialTwoShared A strategy hwin,
    none)

@[simp] theorem literalCombinedFreshPendingOnlyInitial_freshness
    (package : Package A strategy hwin (initial := initial)) :
    ((package.literalCombinedFreshPendingOnlyInitialOne A strategy hwin).2.1.1,
      (package.literalCombinedFreshPendingOnlyInitialTwo A strategy hwin
        ).2.1.1) =
      decoratedFreshnessBothInitial A strategy hwin (package.policy.run []) :=
  rfl

@[simp] theorem literalCombinedFreshPendingOnlyInitial_keys
    (package : Package A strategy hwin (initial := initial)) :
    ((package.literalCombinedFreshPendingOnlyInitialOne A strategy hwin
        ).2.1.2.1.1,
      (package.literalCombinedFreshPendingOnlyInitialTwo A strategy hwin
        ).2.1.2.1.1) =
      (package.literalCombinedFreshPendingOnlyInitialKey A strategy hwin,
        package.literalCombinedFreshPendingOnlyInitialKey A strategy hwin) :=
  rfl

/-- The initial finite table pair satisfies the leader-free freshness
invariant. -/
theorem literalCombinedFreshPendingOnlyInitial_aligned
    (package : Package A strategy hwin (initial := initial)) :
    DecoratedFreshnessAligned A strategy hwin
      (package.literalCombinedFreshPendingOnlyInitialOne A strategy hwin
        ).2.1.1
      (package.literalCombinedFreshPendingOnlyInitialTwo A strategy hwin
        ).2.1.1 := by
  simpa [literalCombinedFreshPendingOnlyInitialOne,
    literalCombinedFreshPendingOnlyInitialTwo,
    literalCombinedFreshPendingOnlyInitialOneShared,
    literalCombinedFreshPendingOnlyInitialTwoShared,
    literalCrossCombinedFreshOneSharedAt,
    literalCrossCombinedFreshTwoSharedAt] using
      (decoratedFreshnessBothInitial_aligned A strategy hwin
        (package.policy.run []))

/-! ## The fixed controller and its canonical trace word -/

/-- The pending-only acknowledged Mealy controller with no residual initial
control arguments. -/
noncomputable def literalCombinedFreshPendingOnlyRootController
    (package : Package A strategy hwin (initial := initial)) :
    FinitePairedMealyController In₁ In₂ Out₁ Out₂ :=
  package.literalCombinedFreshPendingOnlyController A strategy hwin
    (package.literalCombinedFreshPendingOnlyInitialOne A strategy hwin)
    (package.literalCombinedFreshPendingOnlyInitialTwo A strategy hwin)

/-- Moore-facing finite physical controller consumed by direct readback. -/
noncomputable def literalCombinedFreshPendingOnlyRootPhysicalController
    (package : Package A strategy hwin (initial := initial)) :
    FinitePairedPhysicalController In₁ In₂ Out₁ Out₂ :=
  (package.literalCombinedFreshPendingOnlyRootController A strategy hwin
    ).mooreize

/-- The already proved acknowledgement/controller simulation, specialized to
the concrete root pair and converted to the physical Moore interface. -/
noncomputable def literalCombinedFreshPendingOnlyRootTraceInvariant
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) :
    (package.literalCombinedFreshPendingOnlyRootPhysicalController A strategy
      hwin).LiteralCrossGraphTraceInvariant env :=
  (package.literalCombinedFreshPendingOnlyMealyTraceInvariant A strategy hwin
    (package.literalCombinedFreshPendingOnlyInitialOne A strategy hwin)
    (package.literalCombinedFreshPendingOnlyInitialTwo A strategy hwin) env
    ).toMooreTraceInvariant _

/-- The actual physical word is exactly the canonical table-only reference
word.  This consumes all relay-ID and acknowledgement bookkeeping. -/
theorem literalCombinedFreshPendingOnlyRootTraceWord_eq_referenceWord
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) :
    let controller :=
      package.literalCombinedFreshPendingOnlyRootPhysicalController A strategy
        hwin
    controller.globalMachine.globalMachineTraceWord controller.globalOutputOne
        controller.globalOutputTwo env =
      (package.literalCombinedFreshPendingOnlyRootTraceInvariant A strategy
        hwin env).referenceWord controller := by
  dsimp only
  exact
    (package.literalCombinedFreshPendingOnlyRootTraceInvariant A strategy hwin
      env).globalMachineTraceWord_eq_referenceWord _

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
