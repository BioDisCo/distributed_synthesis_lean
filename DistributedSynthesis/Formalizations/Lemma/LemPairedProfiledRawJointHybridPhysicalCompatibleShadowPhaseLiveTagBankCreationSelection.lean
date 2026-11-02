/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteDependentDeferredSelectionProduct
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveTagBankCreationPrefix

/-!
# Selected-owner bridge from the tag creation carrier to a finite Pi bank

The informed creation carrier stores one current tag fibre.  The endpoint
that does not know that tag may instead evolve the dependent product of all
owner candidates.  This file instantiates the generic Pi/Sigma adapter and
proves the smallest exact synchronization relation:

* the product member at the selected tag is the owner stored in the current
  carrier, including its unresolved member bit;
* one homogeneous step preserves that equality; and
* the two selected candidate outputs are definitionally the same.

This does not assert that outputs of *different* tag fibres agree.  That is
exactly `BlindOutputCoherentAt`, the remaining law needed to project the Pi
bank to one physical blind output.  Nor does this imply the cross-table
anti-mosaic law required by a later `.both`/strict switch.
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
  ProfiledRawJointHybridShadowPhaseLiveTailOnePending.{u, v, x, y, s, 0, 0}
    A strategy hwin tag

private abbrev TwoPending (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailTwoPending.{u, v, x, y, s, 0, 0}
    A strategy hwin tag

private abbrev CurrentPair (tag : Tag A strategy hwin) :=
  OnePending A strategy hwin tag × TwoPending A strategy hwin tag

private abbrev RightOwner (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailFrontierOneShared A strategy hwin tag

private abbrev LeftOwner (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailFrontierTwoShared A strategy hwin tag

/-! ## Right-owner Pi bank / left-tag current carrier -/

private abbrev RightBlind (tag : Tag A strategy hwin) :=
  Bool × RightOwner A strategy hwin tag

/-- Abstract homogeneous transition system whose blind component is one
right-owner candidate and whose informed component is the full current pair.
The latter sees the two inputs and performs the already proved left-tag
creation step. -/
noncomputable def profiledRawJointHybridShadowPhaseLiveRightOwnerSelectionFamily :
    FiniteAcknowledgedDelayedCarrier.FiniteDependentDeferredSelectionFamily
      (Tag A strategy hwin) In₁ In₂ Out₁ Out₁ where
  Blind := RightBlind A strategy hwin
  Informed := CurrentPair A strategy hwin
  blindFinite _ := by classical infer_instance
  informedFinite _ := by classical infer_instance
  blindStep tag blind input :=
    let next :=
      profiledRawJointHybridShadowPhaseLiveTailRightSharedStep A strategy hwin
        tag blind.2.1 blind.1 blind.2.2 input
    ((blind.1, ⟨blind.2.1, next.1⟩), next.2)
  informedStep tag current inputTwo _blind inputOne :=
    profiledRawJointHybridShadowPhaseLiveLeftTagCreationStep A strategy hwin tag
      current (inputOne, inputTwo)

/-- The selected Pi member is literally the member bit and right owner stored
inside the current pending pair. -/
def ProfiledRawJointHybridShadowPhaseLiveRightSelectedOwnerRel
    (tag : Tag A strategy hwin) (blind : RightBlind A strategy hwin tag)
    (current : CurrentPair A strategy hwin tag) : Prop :=
  blind = (current.1.1, current.1.2.1.baseShared)

theorem
    profiledRawJointHybridShadowPhaseLiveRightSelectedOwnerRel_step
    (tag : Tag A strategy hwin) (blind : RightBlind A strategy hwin tag)
    (current : CurrentPair A strategy hwin tag)
    (inputOne : In₁) (inputTwo : In₂)
    (hrel :
      ProfiledRawJointHybridShadowPhaseLiveRightSelectedOwnerRel A strategy
        hwin tag blind current) :
    ProfiledRawJointHybridShadowPhaseLiveRightSelectedOwnerRel A strategy hwin
      tag
      ((profiledRawJointHybridShadowPhaseLiveRightOwnerSelectionFamily A
        strategy hwin).blindStep tag blind inputOne).1
      ((profiledRawJointHybridShadowPhaseLiveRightOwnerSelectionFamily A
        strategy hwin).informedStep tag current inputTwo blind inputOne).1 := by
  subst blind
  rfl

/-- At related selected states the blind member and informed current carrier
propose exactly the same owner output. -/
theorem
    profiledRawJointHybridShadowPhaseLiveRightSelectedOwnerRel_output_eq
    (tag : Tag A strategy hwin) (blind : RightBlind A strategy hwin tag)
    (current : CurrentPair A strategy hwin tag)
    (inputOne : In₁) (inputTwo : In₂)
    (hrel :
      ProfiledRawJointHybridShadowPhaseLiveRightSelectedOwnerRel A strategy
        hwin tag blind current) :
    ((profiledRawJointHybridShadowPhaseLiveRightOwnerSelectionFamily A strategy
        hwin).blindStep tag blind inputOne).2 =
      ((profiledRawJointHybridShadowPhaseLiveRightOwnerSelectionFamily A
        strategy hwin).informedStep tag current inputTwo blind inputOne).2 := by
  subst blind
  rfl

/-- The generic arbitrary-prefix theorem now applies with no further semantic
premise: selected-owner equality is maintained for every finite word. -/
theorem
    profiledRawJointHybridShadowPhaseLiveRightOwnerSelection_rel_run
    (state :
      (profiledRawJointHybridShadowPhaseLiveRightOwnerSelectionFamily A
        strategy hwin).DeferredSelectionState)
    (inputs : List (In₁ × In₂))
    (hrel :
      (profiledRawJointHybridShadowPhaseLiveRightOwnerSelectionFamily A
        strategy hwin).SelectedRel
          (ProfiledRawJointHybridShadowPhaseLiveRightSelectedOwnerRel A strategy
            hwin) state) :
    (profiledRawJointHybridShadowPhaseLiveRightOwnerSelectionFamily A strategy
      hwin).SelectedRel
        (ProfiledRawJointHybridShadowPhaseLiveRightSelectedOwnerRel A strategy
          hwin)
        ((profiledRawJointHybridShadowPhaseLiveRightOwnerSelectionFamily A
          strategy hwin).run state inputs) := by
  apply
    (profiledRawJointHybridShadowPhaseLiveRightOwnerSelectionFamily A strategy
      hwin).selectedRel_run
      (ProfiledRawJointHybridShadowPhaseLiveRightSelectedOwnerRel A strategy
        hwin)
  · exact
      profiledRawJointHybridShadowPhaseLiveRightSelectedOwnerRel_step A strategy
        hwin
  · exact hrel

/-! ## Left-owner mirror / right-tag current carrier -/

private abbrev LeftBlind (tag : Tag A strategy hwin) :=
  Bool × LeftOwner A strategy hwin tag

noncomputable def profiledRawJointHybridShadowPhaseLiveLeftOwnerSelectionFamily :
    FiniteAcknowledgedDelayedCarrier.FiniteDependentDeferredSelectionFamily
      (Tag A strategy hwin) In₂ In₁ Out₂ Out₂ where
  Blind := LeftBlind A strategy hwin
  Informed := CurrentPair A strategy hwin
  blindFinite _ := by classical infer_instance
  informedFinite _ := by classical infer_instance
  blindStep tag blind input :=
    let next :=
      profiledRawJointHybridShadowPhaseLiveTailLeftSharedStep A strategy hwin tag
        blind.2.1 blind.1 blind.2.2 input
    ((blind.1, ⟨blind.2.1, next.1⟩), next.2)
  informedStep tag current inputOne _blind inputTwo :=
    profiledRawJointHybridShadowPhaseLiveRightTagCreationStep A strategy hwin
      tag current (inputOne, inputTwo)

def ProfiledRawJointHybridShadowPhaseLiveLeftSelectedOwnerRel
    (tag : Tag A strategy hwin) (blind : LeftBlind A strategy hwin tag)
    (current : CurrentPair A strategy hwin tag) : Prop :=
  blind = (current.2.1, current.2.2.1.baseShared)

theorem
    profiledRawJointHybridShadowPhaseLiveLeftSelectedOwnerRel_step
    (tag : Tag A strategy hwin) (blind : LeftBlind A strategy hwin tag)
    (current : CurrentPair A strategy hwin tag)
    (inputTwo : In₂) (inputOne : In₁)
    (hrel :
      ProfiledRawJointHybridShadowPhaseLiveLeftSelectedOwnerRel A strategy hwin
        tag blind current) :
    ProfiledRawJointHybridShadowPhaseLiveLeftSelectedOwnerRel A strategy hwin tag
      ((profiledRawJointHybridShadowPhaseLiveLeftOwnerSelectionFamily A strategy
        hwin).blindStep tag blind inputTwo).1
      ((profiledRawJointHybridShadowPhaseLiveLeftOwnerSelectionFamily A strategy
        hwin).informedStep tag current inputOne blind inputTwo).1 := by
  subst blind
  rfl

theorem
    profiledRawJointHybridShadowPhaseLiveLeftSelectedOwnerRel_output_eq
    (tag : Tag A strategy hwin) (blind : LeftBlind A strategy hwin tag)
    (current : CurrentPair A strategy hwin tag)
    (inputTwo : In₂) (inputOne : In₁)
    (hrel :
      ProfiledRawJointHybridShadowPhaseLiveLeftSelectedOwnerRel A strategy hwin
        tag blind current) :
    ((profiledRawJointHybridShadowPhaseLiveLeftOwnerSelectionFamily A strategy
        hwin).blindStep tag blind inputTwo).2 =
      ((profiledRawJointHybridShadowPhaseLiveLeftOwnerSelectionFamily A strategy
        hwin).informedStep tag current inputOne blind inputTwo).2 := by
  subst blind
  rfl

theorem
    profiledRawJointHybridShadowPhaseLiveLeftOwnerSelection_rel_run
    (state :
      (profiledRawJointHybridShadowPhaseLiveLeftOwnerSelectionFamily A strategy
        hwin).DeferredSelectionState)
    (inputs : List (In₂ × In₁))
    (hrel :
      (profiledRawJointHybridShadowPhaseLiveLeftOwnerSelectionFamily A strategy
        hwin).SelectedRel
          (ProfiledRawJointHybridShadowPhaseLiveLeftSelectedOwnerRel A strategy
            hwin) state) :
    (profiledRawJointHybridShadowPhaseLiveLeftOwnerSelectionFamily A strategy
      hwin).SelectedRel
        (ProfiledRawJointHybridShadowPhaseLiveLeftSelectedOwnerRel A strategy
          hwin)
        ((profiledRawJointHybridShadowPhaseLiveLeftOwnerSelectionFamily A
          strategy hwin).run state inputs) := by
  apply
    (profiledRawJointHybridShadowPhaseLiveLeftOwnerSelectionFamily A strategy
      hwin).selectedRel_run
      (ProfiledRawJointHybridShadowPhaseLiveLeftSelectedOwnerRel A strategy hwin)
  · exact
      profiledRawJointHybridShadowPhaseLiveLeftSelectedOwnerRel_step A strategy
        hwin
  · exact hrel

/-! ## Exact residual for one physical Pi-bank output -/

/-- Once all blind candidate outputs are coherent, any fixed finite projection
is also the output of the current selected right owner.  This theorem exposes
the only additional premise; it does not derive it. -/
theorem
    profiledRawJointHybridShadowPhaseLiveRightOwnerSelection_projected_output
    (outputKey : Tag A strategy hwin)
    (state :
      (profiledRawJointHybridShadowPhaseLiveRightOwnerSelectionFamily A strategy
        hwin).DeferredSelectionState)
    (input : In₁ × In₂)
    (hrel :
      (profiledRawJointHybridShadowPhaseLiveRightOwnerSelectionFamily A strategy
        hwin).SelectedRel
          (ProfiledRawJointHybridShadowPhaseLiveRightSelectedOwnerRel A strategy
            hwin) state)
    (hcoherent :
      (profiledRawJointHybridShadowPhaseLiveRightOwnerSelectionFamily A strategy
        hwin).BlindOutputCoherentAt state.1 input.1) :
    ((profiledRawJointHybridShadowPhaseLiveRightOwnerSelectionFamily A strategy
        hwin).blindNoRecv outputKey state.1 input.1).2 =
      ((profiledRawJointHybridShadowPhaseLiveRightOwnerSelectionFamily A strategy
        hwin).informedStep state.2.1 state.2.2 input.2
          (state.1 state.2.1) input.1).2 := by
  calc
    _ = ((profiledRawJointHybridShadowPhaseLiveRightOwnerSelectionFamily A
          strategy hwin).blindStep state.2.1 (state.1 state.2.1) input.1).2 :=
      (profiledRawJointHybridShadowPhaseLiveRightOwnerSelectionFamily A strategy
        hwin).blindNoRecv_output_eq_selected outputKey state.1 state.2 input.1
          hcoherent
    _ = _ :=
      profiledRawJointHybridShadowPhaseLiveRightSelectedOwnerRel_output_eq A
        strategy hwin state.2.1 (state.1 state.2.1) state.2.2 input.1 input.2
          hrel

/-- Mirror residual. -/
theorem
    profiledRawJointHybridShadowPhaseLiveLeftOwnerSelection_projected_output
    (outputKey : Tag A strategy hwin)
    (state :
      (profiledRawJointHybridShadowPhaseLiveLeftOwnerSelectionFamily A strategy
        hwin).DeferredSelectionState)
    (input : In₂ × In₁)
    (hrel :
      (profiledRawJointHybridShadowPhaseLiveLeftOwnerSelectionFamily A strategy
        hwin).SelectedRel
          (ProfiledRawJointHybridShadowPhaseLiveLeftSelectedOwnerRel A strategy
            hwin) state)
    (hcoherent :
      (profiledRawJointHybridShadowPhaseLiveLeftOwnerSelectionFamily A strategy
        hwin).BlindOutputCoherentAt state.1 input.1) :
    ((profiledRawJointHybridShadowPhaseLiveLeftOwnerSelectionFamily A strategy
        hwin).blindNoRecv outputKey state.1 input.1).2 =
      ((profiledRawJointHybridShadowPhaseLiveLeftOwnerSelectionFamily A strategy
        hwin).informedStep state.2.1 state.2.2 input.2
          (state.1 state.2.1) input.1).2 := by
  calc
    _ = ((profiledRawJointHybridShadowPhaseLiveLeftOwnerSelectionFamily A
          strategy hwin).blindStep state.2.1 (state.1 state.2.1) input.1).2 :=
      (profiledRawJointHybridShadowPhaseLiveLeftOwnerSelectionFamily A strategy
        hwin).blindNoRecv_output_eq_selected outputKey state.1 state.2 input.1
          hcoherent
    _ = _ :=
      profiledRawJointHybridShadowPhaseLiveLeftSelectedOwnerRel_output_eq A
        strategy hwin state.2.1 (state.1 state.2.1) state.2.2 input.1 input.2
          hrel

end

end DetParityAutomaton

end DistributedSynthesis
