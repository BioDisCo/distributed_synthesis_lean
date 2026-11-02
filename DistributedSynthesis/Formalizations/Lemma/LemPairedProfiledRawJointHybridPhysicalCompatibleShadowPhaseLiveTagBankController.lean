/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteAcknowledgedExactClosingDeferredFamily
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveTagBankHandoff
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveTailController

/-!
# The finite dependent controller bank selected by a delivered tail tag

Each finite delayed tag indexes one complete acknowledged exact-closing
controller fibre.  Sigma-packing the fibres gives the two finite process-local
control types.  A later delivery merely copies the common tag and installs the
canonical roots of that fibre; it does not inspect a graph, leader bit,
strict-leader bit, history, or semantic view.

The fallback records below totalize impossible malformed receiver states.
They are computed from the two literal physical lanes already proved present
at the tagged root.  On the invariant, live receiver branches never consult
these fallbacks.
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

private abbrev OneControl (tag : Tag A strategy hwin) :=
  FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
    (ProfiledRawJointHybridShadowPhaseLiveTailOneShared A strategy hwin tag)
    PUnit PUnit

private abbrev TwoControl (tag : Tag A strategy hwin) :=
  FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
    (ProfiledRawJointHybridShadowPhaseLiveTailTwoShared A strategy hwin tag)
    PUnit PUnit

private abbrev RightOutput (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailRightReceiverOutput A strategy hwin
    tag

private abbrev LeftOutput (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailLeftReceiverOutput A strategy hwin
    tag

/-! ## Total fallbacks from the literal tagged root -/

noncomputable def ProfiledRawJointHybridShadowPhaseLiveTag.initialRightMove
    (tag : Tag A strategy hwin) :
    ProfiledRawJointRightPhysicalSiblingMove A :=
  Classical.choose (tag.tailRoot_lanes A strategy hwin)

noncomputable def ProfiledRawJointHybridShadowPhaseLiveTag.initialLeftMove
    (tag : Tag A strategy hwin) :
    ProfiledRawJointLeftPhysicalSiblingMove A :=
  Classical.choose (Classical.choose_spec
    (tag.tailRoot_lanes A strategy hwin))

theorem ProfiledRawJointHybridShadowPhaseLiveTag.initialMoves_eq
    (tag : Tag A strategy hwin) :
    (tag.tailRoot A strategy hwin).1.2 =
      (some (tag.initialRightMove A strategy hwin),
        some (tag.initialLeftMove A strategy hwin)) :=
  Classical.choose_spec (Classical.choose_spec
    (tag.tailRoot_lanes A strategy hwin))

/-- A well-typed right record used only if an impossible inert receiver is
encountered. -/
noncomputable def
    ProfiledRawJointHybridShadowPhaseLiveTag.fallbackRightOutput
    (tag : Tag A strategy hwin) : RightOutput A strategy hwin tag :=
  let move := tag.initialRightMove A strategy hwin
  (profiledRawJointHybridShadowPhaseLiveTailRightReceiverStepFor A strategy
    hwin tag (tag.tailRoot A strategy hwin) move
      (move.memberController A false).initial .first
      (profiledRawJointHybridShadowPhaseLiveTailSuccessorRightMonitor A strategy
        hwin (tag := tag) move false).initial
      (default, default)).1

/-- Left mirror. -/
noncomputable def
    ProfiledRawJointHybridShadowPhaseLiveTag.fallbackLeftOutput
    (tag : Tag A strategy hwin) : LeftOutput A strategy hwin tag :=
  let move := tag.initialLeftMove A strategy hwin
  (profiledRawJointHybridShadowPhaseLiveTailLeftReceiverStepFor A strategy hwin
    tag (tag.tailRoot A strategy hwin) move
      (move.memberController A false).initial .first
      (profiledRawJointHybridShadowPhaseLiveTailSuccessorLeftMonitor A strategy
        hwin (tag := tag) move false).initial
      (default, default)).1

/-! ## The tag-indexed deferred family -/

/-- Every finite delayed tag indexes the already assembled canonical
acknowledged controller.  `Rel := True` is only the generic exact-close relay
law; semantic tail correctness is carried by the separate table/tracked
invariants. -/
noncomputable def profiledRawJointHybridShadowPhaseLiveTagDeferredFamily :
    FiniteAcknowledgedDelayedCarrier.FiniteDeferredExactClosingFamily
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
      (Tag A strategy hwin) where
  SharedOne tag :=
    ProfiledRawJointHybridShadowPhaseLiveTailOneShared A strategy hwin tag
  PayloadOne _ := PUnit
  RecurrentOne _ := PUnit
  SharedTwo tag :=
    ProfiledRawJointHybridShadowPhaseLiveTailTwoShared A strategy hwin tag
  PayloadTwo _ := PUnit
  RecurrentTwo _ := PUnit
  oneFinite _ := by classical infer_instance
  twoFinite _ := by classical infer_instance
  initialOne tag := .inl (tag.initialOne A strategy hwin)
  initialTwo tag := .inl (tag.initialTwo A strategy hwin)
  pendingStepOne tag :=
    profiledRawJointHybridShadowPhaseLiveTailOnePendingStep A strategy hwin tag
  recurrentStepOne _ :=
    profiledRawJointHybridShadowPhaseLiveTailRecurrentStepOne
  pendingStepTwo tag :=
    profiledRawJointHybridShadowPhaseLiveTailTwoPendingStep A strategy hwin tag
  recurrentStepTwo _ :=
    profiledRawJointHybridShadowPhaseLiveTailRecurrentStepTwo
  openRecvOne tag :=
    profiledRawJointHybridShadowPhaseLiveTailOpenRecvOne A strategy hwin tag
      (tag.initialOne A strategy hwin)
      (tag.fallbackLeftOutput A strategy hwin)
      (tag.fallbackRightOutput A strategy hwin)
  openRecvTwo tag :=
    profiledRawJointHybridShadowPhaseLiveTailOpenRecvTwo A strategy hwin tag
      (tag.initialTwo A strategy hwin)
      (tag.fallbackLeftOutput A strategy hwin)
      (tag.fallbackRightOutput A strategy hwin)
  close tag :=
    profiledRawJointHybridShadowPhaseLiveTailClose A strategy hwin tag
      (tag.initialOne A strategy hwin) (tag.initialTwo A strategy hwin)
      (tag.fallbackLeftOutput A strategy hwin)
      (tag.fallbackRightOutput A strategy hwin)
  Rel _ _ _ := True
  laws tag :=
    profiledRawJointHybridShadowPhaseLiveTailForkLaws A strategy hwin tag
      (tag.initialOne A strategy hwin) (tag.initialTwo A strategy hwin)
      (tag.fallbackLeftOutput A strategy hwin)
      (tag.fallbackRightOutput A strategy hwin)

abbrev ProfiledRawJointHybridShadowPhaseLiveTagBankOneControl :=
  Σ tag : Tag A strategy hwin, OneControl A strategy hwin tag

abbrev ProfiledRawJointHybridShadowPhaseLiveTagBankTwoControl :=
  Σ tag : Tag A strategy hwin, TwoControl A strategy hwin tag

noncomputable instance :
    Fintype
      (ProfiledRawJointHybridShadowPhaseLiveTagBankOneControl A strategy hwin) :=
  by classical infer_instance

noncomputable instance :
    Fintype
      (ProfiledRawJointHybridShadowPhaseLiveTagBankTwoControl A strategy hwin) :=
  by classical infer_instance

/-! ## Delayed activation is a finite tag copy -/

noncomputable def profiledRawJointHybridShadowPhaseLiveTagBankInitialOne
    (tag : Tag A strategy hwin) :
    ProfiledRawJointHybridShadowPhaseLiveTagBankOneControl A strategy hwin :=
  ⟨tag, .inl (tag.initialOne A strategy hwin)⟩

noncomputable def profiledRawJointHybridShadowPhaseLiveTagBankInitialTwo
    (tag : Tag A strategy hwin) :
    ProfiledRawJointHybridShadowPhaseLiveTagBankTwoControl A strategy hwin :=
  ⟨tag, .inl (tag.initialTwo A strategy hwin)⟩

@[simp] theorem profiledRawJointHybridShadowPhaseLiveTagBankInitialOne_key
    (tag : Tag A strategy hwin) :
    (profiledRawJointHybridShadowPhaseLiveTagBankInitialOne A strategy hwin
      tag).1 = tag :=
  rfl

@[simp] theorem profiledRawJointHybridShadowPhaseLiveTagBankInitialTwo_key
    (tag : Tag A strategy hwin) :
    (profiledRawJointHybridShadowPhaseLiveTagBankInitialTwo A strategy hwin
      tag).1 = tag :=
  rfl

/-- Activate both local bank roots from the tag carried by a strict-left
handoff.  In the operational machine each projection is installed at its
corresponding local receive; the pair is the proof-side equality interface. -/
noncomputable def
    profiledRawJointHybridActivateDeliveredLeftShadowPhaseLiveBank
    (delivered :
      ProfiledRawJointHybridLeftShadowPhaseLiveHandoff A strategy hwin) :
    ProfiledRawJointHybridShadowPhaseLiveTagBankOneControl A strategy hwin ×
      ProfiledRawJointHybridShadowPhaseLiveTagBankTwoControl A strategy hwin :=
  (profiledRawJointHybridShadowPhaseLiveTagBankInitialOne A strategy hwin
      delivered.tag,
    profiledRawJointHybridShadowPhaseLiveTagBankInitialTwo A strategy hwin
      delivered.tag)

/-- Strict-right mirror. -/
noncomputable def
    profiledRawJointHybridActivateDeliveredRightShadowPhaseLiveBank
    (delivered :
      ProfiledRawJointHybridRightShadowPhaseLiveHandoff A strategy hwin) :
    ProfiledRawJointHybridShadowPhaseLiveTagBankOneControl A strategy hwin ×
      ProfiledRawJointHybridShadowPhaseLiveTagBankTwoControl A strategy hwin :=
  (profiledRawJointHybridShadowPhaseLiveTagBankInitialOne A strategy hwin
      delivered.tag,
    profiledRawJointHybridShadowPhaseLiveTagBankInitialTwo A strategy hwin
      delivered.tag)

@[simp] theorem
    profiledRawJointHybridActivateDeliveredLeftShadowPhaseLiveBank_keys
    (delivered :
      ProfiledRawJointHybridLeftShadowPhaseLiveHandoff A strategy hwin) :
    (profiledRawJointHybridActivateDeliveredLeftShadowPhaseLiveBank A strategy
      hwin delivered).1.1 =
      (profiledRawJointHybridActivateDeliveredLeftShadowPhaseLiveBank A strategy
        hwin delivered).2.1 :=
  rfl

@[simp] theorem
    profiledRawJointHybridActivateDeliveredRightShadowPhaseLiveBank_keys
    (delivered :
      ProfiledRawJointHybridRightShadowPhaseLiveHandoff A strategy hwin) :
    (profiledRawJointHybridActivateDeliveredRightShadowPhaseLiveBank A strategy
      hwin delivered).1.1 =
      (profiledRawJointHybridActivateDeliveredRightShadowPhaseLiveBank A
        strategy hwin delivered).2.1 :=
  rfl

end

end DetParityAutomaton

end DistributedSynthesis
