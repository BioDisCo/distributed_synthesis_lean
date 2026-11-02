/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveTailSingleTableBoth

/-!
# Pending-level simultaneous output in one tagged tail fibre

The phase-live pending controls already contain every finite datum needed by a
simultaneous close.  In a right-live phase process one's `baseShared` is the
owner and process two's selected receiver is its matching receiver; in a
left-live phase the roles are mirrored.

Both receive handlers can inspect the same process-one phase bit: process one
stores it locally and process two receives the complete process-one control.
They therefore select the same live table without knowing which process is a
strict leader before the receive.  No executable definition below takes a
graph, orientation, leader bit, history, or semantic view.
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

private abbrev Tag :=
  ProfiledRawJointHybridShadowPhaseLiveTag A strategy hwin

private abbrev OnePending (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailOnePending A strategy hwin tag

private abbrev TwoPending (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailTwoPending A strategy hwin tag

private abbrev RightOutput (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailRightReceiverOutput A strategy hwin
    tag

private abbrev LeftOutput (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailLeftReceiverOutput A strategy hwin
    tag

/-! ## Pending controls expose one aligned live table -/

def ProfiledRawJointHybridShadowPhaseLiveTailRightPendingAligned
    (tag : Tag A strategy hwin) (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) : Prop :=
  ProfiledRawJointHybridShadowPhaseLiveTailRightSingleTableAligned A strategy
    hwin tag one.2.1.baseShared (two.2.1.receiver two.1)

def ProfiledRawJointHybridShadowPhaseLiveTailLeftPendingAligned
    (tag : Tag A strategy hwin) (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) : Prop :=
  ProfiledRawJointHybridShadowPhaseLiveTailLeftSingleTableAligned A strategy
    hwin tag two.2.1.baseShared (one.2.1.receiver one.1)

/-- The public finite local phase in process one's pending control selects the
one table whose owner/receiver alignment is asserted.  The constructor names
are proof-side only; the executable selector below reads just that bit. -/
inductive ProfiledRawJointHybridShadowPhaseLiveTailPendingAligned
    (tag : Tag A strategy hwin) (one : OnePending A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) : Prop
  | right
      (phase : one.2.1.localPhase = false)
      (aligned :
        ProfiledRawJointHybridShadowPhaseLiveTailRightPendingAligned A strategy
          hwin tag one two)
  | left
      (phase : one.2.1.localPhase = true)
      (aligned :
        ProfiledRawJointHybridShadowPhaseLiveTailLeftPendingAligned A strategy
          hwin tag one two)

/-! ## Local handlers -/

noncomputable def
    profiledRawJointHybridShadowPhaseLiveTailPendingBothOutputOne
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag) (inputOne : In₁)
    (two : TwoPending A strategy hwin tag) (inputTwo : In₂) : Out₁ :=
  if one.2.1.localPhase then
    profiledRawJointHybridShadowPhaseLiveTailLeftSingleTableBothOutputOne A
      strategy hwin tag fallbackLeft (one.2.1.receiver one.1)
        two.2.1.baseShared (inputOne, inputTwo)
  else
    profiledRawJointHybridShadowPhaseLiveTailRightSingleTableBothOutputOne A
      strategy hwin tag fallbackRight one.2.1.baseShared
        (two.2.1.receiver two.1) (inputOne, inputTwo)

/-- Process-two executes the same finite selector after receiving process
one's control.  Argument order matches a process-two receive handler. -/
noncomputable def
    profiledRawJointHybridShadowPhaseLiveTailPendingBothOutputTwo
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (two : TwoPending A strategy hwin tag) (inputTwo : In₂)
    (one : OnePending A strategy hwin tag) (inputOne : In₁) : Out₂ :=
  if one.2.1.localPhase then
    profiledRawJointHybridShadowPhaseLiveTailLeftSingleTableBothOutputTwo A
      strategy hwin tag fallbackLeft two.2.1.baseShared
        (one.2.1.receiver one.1) (inputOne, inputTwo)
  else
    profiledRawJointHybridShadowPhaseLiveTailRightSingleTableBothOutputTwo A
      strategy hwin tag fallbackRight (two.2.1.receiver two.1)
        one.2.1.baseShared (inputOne, inputTwo)

/-! ## Exact selected-record equations -/

theorem
    ProfiledRawJointHybridShadowPhaseLiveTailPendingAligned.bothOutputs_eq_rightRecord
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag) (two : TwoPending A strategy hwin tag)
    (phase : one.2.1.localPhase = false)
    (aligned :
      ProfiledRawJointHybridShadowPhaseLiveTailRightPendingAligned A strategy
        hwin tag one two)
    (input : In₁ × In₂) :
    (profiledRawJointHybridShadowPhaseLiveTailPendingBothOutputOne A strategy
        hwin tag fallbackLeft fallbackRight one input.1 two input.2,
      profiledRawJointHybridShadowPhaseLiveTailPendingBothOutputTwo A strategy
        hwin tag fallbackLeft fallbackRight two input.2 one input.1) =
      let record :=
        profiledRawJointHybridShadowPhaseLiveTailRightSingleTableRecord A
          strategy hwin tag fallbackRight one.2.1.baseShared
            (two.2.1.receiver two.1) (input.2, input.1)
      (pairedRightClosingForRow .both record.physical,
        pairedRightInformedForRow .both record.physical) := by
  simp only
    [profiledRawJointHybridShadowPhaseLiveTailPendingBothOutputOne,
      profiledRawJointHybridShadowPhaseLiveTailPendingBothOutputTwo, phase,
      Bool.false_eq_true, ↓reduceIte]
  exact
    ProfiledRawJointHybridShadowPhaseLiveTailRightSingleTableAligned.bothOutputs_eq_closingRecord
      A strategy hwin tag fallbackRight one.2.1.baseShared
        (two.2.1.receiver two.1) aligned input

theorem
    ProfiledRawJointHybridShadowPhaseLiveTailPendingAligned.bothOutputs_eq_leftRecord
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag) (two : TwoPending A strategy hwin tag)
    (phase : one.2.1.localPhase = true)
    (aligned :
      ProfiledRawJointHybridShadowPhaseLiveTailLeftPendingAligned A strategy
        hwin tag one two)
    (input : In₁ × In₂) :
    (profiledRawJointHybridShadowPhaseLiveTailPendingBothOutputOne A strategy
        hwin tag fallbackLeft fallbackRight one input.1 two input.2,
      profiledRawJointHybridShadowPhaseLiveTailPendingBothOutputTwo A strategy
        hwin tag fallbackLeft fallbackRight two input.2 one input.1) =
      let record :=
        profiledRawJointHybridShadowPhaseLiveTailLeftSingleTableRecord A strategy
          hwin tag fallbackLeft two.2.1.baseShared (one.2.1.receiver one.1) input
      (pairedLeftInformedForRow .both record.physical,
        pairedLeftClosingForRow .both record.physical) := by
  simp only
    [profiledRawJointHybridShadowPhaseLiveTailPendingBothOutputOne,
      profiledRawJointHybridShadowPhaseLiveTailPendingBothOutputTwo, phase,
      ↓reduceIte]
  exact
    ProfiledRawJointHybridShadowPhaseLiveTailLeftSingleTableAligned.bothOutputs_eq_closingRecord
      A strategy hwin tag fallbackLeft two.2.1.baseShared
        (one.2.1.receiver one.1) aligned input

/-- The pending invariant always exposes exactly one checked simultaneous
record.  This is the compact output seam consumed by the physical trace. -/
theorem
    ProfiledRawJointHybridShadowPhaseLiveTailPendingAligned.exists_bothRecord
    (tag : Tag A strategy hwin) (fallbackLeft : LeftOutput A strategy hwin tag)
    (fallbackRight : RightOutput A strategy hwin tag)
    (one : OnePending A strategy hwin tag) (two : TwoPending A strategy hwin tag)
    (aligned :
      ProfiledRawJointHybridShadowPhaseLiveTailPendingAligned A strategy hwin
        tag one two)
    (input : In₁ × In₂) :
    (∃ record : RightOutput A strategy hwin tag,
        (profiledRawJointHybridShadowPhaseLiveTailPendingBothOutputOne A
            strategy hwin tag fallbackLeft fallbackRight one input.1 two
              input.2,
          profiledRawJointHybridShadowPhaseLiveTailPendingBothOutputTwo A
            strategy hwin tag fallbackLeft fallbackRight two input.2 one
              input.1) =
          (pairedRightClosingForRow .both record.physical,
            pairedRightInformedForRow .both record.physical)) ∨
      (∃ record : LeftOutput A strategy hwin tag,
        (profiledRawJointHybridShadowPhaseLiveTailPendingBothOutputOne A
            strategy hwin tag fallbackLeft fallbackRight one input.1 two
              input.2,
          profiledRawJointHybridShadowPhaseLiveTailPendingBothOutputTwo A
            strategy hwin tag fallbackLeft fallbackRight two input.2 one
              input.1) =
          (pairedLeftInformedForRow .both record.physical,
            pairedLeftClosingForRow .both record.physical)) := by
  cases aligned with
  | right phase haligned =>
      left
      let record :=
        profiledRawJointHybridShadowPhaseLiveTailRightSingleTableRecord A
          strategy hwin tag fallbackRight one.2.1.baseShared
            (two.2.1.receiver two.1) (input.2, input.1)
      exact ⟨record,
        ProfiledRawJointHybridShadowPhaseLiveTailPendingAligned.bothOutputs_eq_rightRecord
          A strategy hwin tag fallbackLeft fallbackRight one two phase haligned
            input⟩
  | left phase haligned =>
      right
      let record :=
        profiledRawJointHybridShadowPhaseLiveTailLeftSingleTableRecord A strategy
          hwin tag fallbackLeft two.2.1.baseShared (one.2.1.receiver one.1)
            input
      exact ⟨record,
        ProfiledRawJointHybridShadowPhaseLiveTailPendingAligned.bothOutputs_eq_leftRecord
          A strategy hwin tag fallbackLeft fallbackRight one two phase haligned
            input⟩

end

end DetParityAutomaton

end DistributedSynthesis
