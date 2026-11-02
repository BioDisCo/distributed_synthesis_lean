/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCrossBothPhysical
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonDecoratedPolicyFreshnessCarrier
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonTailHandoff

/-!
# A fresh staged close at a literal simultaneous cut

At a simultaneous cut the retained literal tables already emit the physical
`.both` record of the freshly selected guarded common pair.  We may therefore
close that pair at its empty right prefix and immediately use the existing
checked staged handoff.  Choosing the right root here is a fixed convention,
not a runtime observation of an orientation or a strict leader.

This construction deliberately does not continue a restarted literal sender
to a second record.  In particular it needs no equation between the sender at
the empty history and at a one-letter history, and it reconstructs none of the
older `Pending` controls.
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

/-! ## The checked fresh close -/

/-- Close the guarded pair stored at one current finite decorated-policy
state.  This is the endpoint-facing form: after a receive the state is in the
local freshness control, so no predecessor state or input history is needed. -/
noncomputable def literalCrossFreshRightStagedCloseAt
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (current : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy
      hwin initial (CrossValid A strategy hwin))
    (blockInput : In₁ × In₂) :
    ProfiledRawJointGuardedCommonRightStagedClose A strategy hwin :=
  let pair := package.pairAt A strategy hwin current
  profiledRawJointGuardedCommonRightStageClose A strategy hwin pair
    (profiledRawJointGuardedCommonRightFiniteStateAfter A strategy hwin pair
      [])
    (blockInput.2, blockInput.1) .both

/-- Close the freshly selected guarded pair at its empty right prefix.

The arguments are exactly the finite successor-policy state and the complete
input pair available at the common cut.  There is no old pending state and no
orientation argument. -/
noncomputable def successorLiteralCrossFreshRightStagedClose
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial (CrossValid A strategy hwin))
    (incoming blockInput : In₁ × In₂) :
    ProfiledRawJointGuardedCommonRightStagedClose A strategy hwin :=
  package.literalCrossFreshRightStagedCloseAt A strategy hwin
    (package.policy.successor state incoming) blockInput

/-- The predecessor-facing and current-state-facing forms are definitionally
the same close. -/
@[simp] theorem successorLiteralCrossFreshRightStagedClose_eq_at
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial (CrossValid A strategy hwin))
    (incoming blockInput : In₁ × In₂) :
    package.successorLiteralCrossFreshRightStagedClose A strategy hwin state
        incoming blockInput =
      package.literalCrossFreshRightStagedCloseAt A strategy hwin
        (package.policy.successor state incoming) blockInput := by
  rfl

/-- On a simultaneous physical round the two honest local freshness maps
compute literally the same staged close from their received finite copies.
This is the operational agreement needed before installing the recurrent
key; no process tests whether it is the strict leader. -/
theorem decoratedFreshnessLocalStep_both_freshRightStagedClose_eq
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (one :
      ProfiledRawJointGuardedCommonDecoratedFreshnessOneState A strategy hwin
        initial)
    (two :
      ProfiledRawJointGuardedCommonDecoratedFreshnessTwoState A strategy hwin
        initial)
    (haligned : DecoratedFreshnessAligned A strategy hwin one two)
    (incoming blockInput : In₁ × In₂) :
    let next := decoratedFreshnessLocalStep A strategy hwin package one two
      incoming .both
    package.literalCrossFreshRightStagedCloseAt A strategy hwin next.1.1
        blockInput =
      package.literalCrossFreshRightStagedCloseAt A strategy hwin next.2.1
        blockInput := by
  dsimp only
  rw [decoratedFreshnessLocalStep_both_states_eq A strategy hwin package one
    two haligned incoming]

/-- The common close computed by either endpoint is the successor close
advertised from the unique pre-round fresh copy. -/
theorem
    decoratedFreshnessLocalStep_both_freshRightStagedClose_eq_successor
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (one :
      ProfiledRawJointGuardedCommonDecoratedFreshnessOneState A strategy hwin
        initial)
    (two :
      ProfiledRawJointGuardedCommonDecoratedFreshnessTwoState A strategy hwin
        initial)
    (haligned : DecoratedFreshnessAligned A strategy hwin one two)
    (incoming blockInput : In₁ × In₂) :
    let current := decoratedFreshnessCurrent A strategy hwin one two
    let next := decoratedFreshnessLocalStep A strategy hwin package one two
      incoming .both
    package.literalCrossFreshRightStagedCloseAt A strategy hwin next.1.1
        blockInput =
      package.successorLiteralCrossFreshRightStagedClose A strategy hwin
        current incoming blockInput := by
  dsimp only
  have hstate := decoratedFreshnessLocalStep_current_eq_successor A strategy
    hwin package one two haligned incoming .both
  have hone :
      (decoratedFreshnessLocalStep A strategy hwin package one two incoming
        .both).1.1 =
        package.policy.successor
          (decoratedFreshnessCurrent A strategy hwin one two) incoming := by
    simpa [decoratedFreshnessCurrent, decoratedFreshnessLocalStep,
      decoratedFreshnessRecvOne] using hstate
  rw [hone]
  rfl

/-- The fresh close carries the advertised successor pair. -/
@[simp] theorem successorLiteralCrossFreshRightStagedClose_pair
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial (CrossValid A strategy hwin))
    (incoming blockInput : In₁ × In₂) :
    (package.successorLiteralCrossFreshRightStagedClose A strategy hwin state
      incoming blockInput).handoff.1 =
        package.nextPairAt A strategy hwin state incoming := by
  simp [successorLiteralCrossFreshRightStagedClose,
    literalCrossFreshRightStagedCloseAt, nextPairAt]

/-- Its entry row is literally the simultaneous row. -/
@[simp] theorem successorLiteralCrossFreshRightStagedClose_row
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial (CrossValid A strategy hwin))
    (incoming blockInput : In₁ × In₂) :
    (package.successorLiteralCrossFreshRightStagedClose A strategy hwin state
      incoming blockInput).row = .both := by
  let pair := package.nextPairAt A strategy hwin state incoming
  simpa [successorLiteralCrossFreshRightStagedClose, pair] using
    (profiledRawJointGuardedCommonRightStageClose_of_prefix_row A strategy
      hwin pair [] (blockInput.2, blockInput.1) .both)

/-- The staged handoff is exactly the checked empty-prefix handoff, rather
than a fallback or a reconstruction of a previous strict prefix. -/
theorem successorLiteralCrossFreshRightStagedClose_handoff
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial (CrossValid A strategy hwin))
    (incoming blockInput : In₁ × In₂) :
    (package.successorLiteralCrossFreshRightStagedClose A strategy hwin state
      incoming blockInput).handoff =
        profiledRawJointGuardedCommonRightPrefixHandoff A strategy hwin
          (package.nextPairAt A strategy hwin state incoming) []
          (blockInput.2, blockInput.1) .both := by
  let pair := package.nextPairAt A strategy hwin state incoming
  simpa [successorLiteralCrossFreshRightStagedClose, pair] using
    (profiledRawJointGuardedCommonRightStageClose_of_prefix_handoff A strategy
      hwin pair [] (blockInput.2, blockInput.1) .both)

/-- Consequently its checked target is the target label of the fresh root
record. -/
theorem successorLiteralCrossFreshRightStagedClose_target
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial (CrossValid A strategy hwin))
    (incoming blockInput : In₁ × In₂) :
    (package.successorLiteralCrossFreshRightStagedClose A strategy hwin state
      incoming blockInput).handoff.2.1 =
        (profiledRawJointGuardedCommonRightPrefixOutput A strategy hwin
          (package.nextPairAt A strategy hwin state incoming) []
          (blockInput.2, blockInput.1)).target .both := by
  rw [package.successorLiteralCrossFreshRightStagedClose_handoff A strategy
    hwin state incoming blockInput]
  rfl

/-! ## Exact physical compatibility -/

/-- The two literal receivers at the simultaneous cut emit exactly the
physical `.both` record whose checked target is stored by the fresh close.

The second equality is the guarded-pair anti-mosaic equation.  Hence choosing
the right staged close loses neither physical coordinate, despite the two
coordinates having been read from independently retained literal tables. -/
theorem currentRightLiteralCrossMismatchInitial_successor_bothOutput_eq_freshRightPhysical
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    {state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial (CrossValid A strategy hwin)}
    (hreachable :
      ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
        initial (CrossValid A strategy hwin) package.policy state)
    (incoming blockInput : In₁ × In₂) (anchor : Bool) :
    let initialState :=
      package.currentRightLiteralCrossMismatchInitial A strategy hwin
        (package.policy.successor state incoming) anchor
    let result :=
      profiledRawJointGuardedCommonLiteralCrossMismatchLocalStep A
        initialState.1 initialState.2 blockInput .both
    let pair := package.nextPairAt A strategy hwin state incoming
    let physical :=
      (pair.rightRootRecord A strategy hwin blockInput).2.1.physical
    (result.1.1, result.2.1) =
      (pairedRightClosingForRow .both physical,
        pairedRightInformedForRow .both physical) := by
  have hcut :=
    package.currentRightLiteralCrossMismatchInitial_successor_bothOutput_eq_cut
      A strategy hwin hreachable incoming blockInput anchor
  dsimp only
  rw [hcut]
  apply Prod.ext
  · rfl
  · exact
      (package.nextPairAt A strategy hwin state incoming).root_outputTwo A
        strategy hwin blockInput

/-- Left-phase installation has the same fixed right-close interpretation.
Thus the fresh convention does not inspect the preceding literal phase. -/
theorem currentLeftLiteralCrossMismatchInitial_successor_bothOutput_eq_freshRightPhysical
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    {state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial (CrossValid A strategy hwin)}
    (hreachable :
      ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
        initial (CrossValid A strategy hwin) package.policy state)
    (incoming blockInput : In₁ × In₂) (anchor : Bool) :
    let initialState :=
      package.currentLeftLiteralCrossMismatchInitial A strategy hwin
        (package.policy.successor state incoming) anchor
    let result :=
      profiledRawJointGuardedCommonLiteralCrossMismatchLocalStep A
        initialState.1 initialState.2 blockInput .both
    let pair := package.nextPairAt A strategy hwin state incoming
    let physical :=
      (pair.rightRootRecord A strategy hwin blockInput).2.1.physical
    (result.1.1, result.2.1) =
      (pairedRightClosingForRow .both physical,
        pairedRightInformedForRow .both physical) := by
  have hcut :=
    package.currentLeftLiteralCrossMismatchInitial_successor_bothOutput_eq_cut
      A strategy hwin hreachable incoming blockInput anchor
  dsimp only
  rw [hcut]
  apply Prod.ext
  · rfl
  · exact
      (package.nextPairAt A strategy hwin state incoming).root_outputTwo A
        strategy hwin blockInput

/-! ## Existing recurrent continuation -/

private abbrev OneControl
    (initialBank : ProfiledRawJointInitialControllerBank A strategy) :=
  ProfiledRawJointGuardedHybridCombinedOneControl A strategy hwin initialBank
    (ProfiledRawJointGuardedCommonTailInitialOne A strategy hwin)
    (ProfiledRawJointGuardedCommonTailExceptionalOne A strategy hwin)

private abbrev TwoControl
    (initialBank : ProfiledRawJointInitialControllerBank A strategy) :=
  ProfiledRawJointGuardedHybridCombinedTwoControl A strategy hwin initialBank
    (ProfiledRawJointGuardedCommonTailInitialTwo A strategy hwin)
    (ProfiledRawJointGuardedCommonTailExceptionalTwo A strategy hwin)

/-- The exact recurrent controls installed after the fresh physical close.
Both are indexed by the same existing combined key.  This is proof-side
pairing of two endpoint-local values, not an executable graph case split. -/
noncomputable def successorLiteralCrossFreshRightContinuation
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial (CrossValid A strategy hwin))
    (incoming blockInput : In₁ × In₂) :
    OneControl A strategy hwin initialBank ×
      TwoControl A strategy hwin initialBank :=
  let close := package.successorLiteralCrossFreshRightStagedClose A strategy
    hwin state incoming blockInput
  let key := profiledRawJointGuardedCommonRightStagedCombinedKey A strategy
    hwin initialBank close
  (.leftReceiver key
      (profiledRawJointGuardedCommonRightStagedInitialLeftReceiver A strategy
        hwin initialBank close),
    .leftOwner key
      (profiledRawJointGuardedCommonRightStagedInitialLeftOwner A strategy hwin
        initialBank close))

/-- The two installed controls use literally the same fresh checked key. -/
theorem successorLiteralCrossFreshRightContinuation_controls
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial (CrossValid A strategy hwin))
    (incoming blockInput : In₁ × In₂) :
    let close := package.successorLiteralCrossFreshRightStagedClose A strategy
      hwin state incoming blockInput
    let key := profiledRawJointGuardedCommonRightStagedCombinedKey A strategy
      hwin initialBank close
    (package.successorLiteralCrossFreshRightContinuation A strategy hwin
        initialBank state incoming blockInput).1 =
        .leftReceiver key
          (profiledRawJointGuardedCommonRightStagedInitialLeftReceiver A
            strategy hwin initialBank close) ∧
      (package.successorLiteralCrossFreshRightContinuation A strategy hwin
        initialBank state incoming blockInput).2 =
        .leftOwner key
          (profiledRawJointGuardedCommonRightStagedInitialLeftOwner A strategy
            hwin initialBank close) := by
  exact ⟨rfl, rfl⟩

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
