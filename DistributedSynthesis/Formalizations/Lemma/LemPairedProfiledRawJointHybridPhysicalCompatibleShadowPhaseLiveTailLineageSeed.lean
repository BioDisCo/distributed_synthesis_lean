/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveTailRootAlignedPath

/-!
# Proof-side lineage seed of a delayed tail tag

Every delayed tag names a literal strict child of one installed common move.
The common code exposes the installed source slot on the strict side, while
the literal child exposes the crossed target slot on the opposite side.  This
file packages those two facts as the seed consumed by the root-aligned tail
path.

The tag side is inspected only while constructing a proof witness.  No map
executed by either process receives the side, a graph, an orientation, or a
leader bit.
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

private abbrev TailState (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailState A strategy hwin tag

/-- The two live roots needed before iterating exact tail transitions. -/
structure ProfiledRawJointHybridShadowPhaseLiveTailLineageSeed
    (tag : Tag A strategy hwin) where
  initialSide : IndexedLineageSide
  initialRoot : ProfiledRawJointThreadRoot A
  childRoot : ProfiledRawJointThreadRoot A
  initial_live :
    let installed :=
      profiledRawJointHybridShadowPhaseLiveInstalled A strategy hwin tag.origin
    let initialCode : ProfiledRawJointHybridCode A :=
      .common ((profiledRawJointCommonWorldFamily A installed.world
        ).incidenceCode A)
    profiledRawJointHybridCurrentSlots A initialSide initialCode () =
      some initialRoot
  child_live :
    profiledRawJointHybridCurrentSlots A
        (profiledRawJointHybridPhysicalCompatibleSideAfter initialSide 1)
        (tag.childCode A strategy hwin).1 () =
      some childRoot

namespace ProfiledRawJointHybridShadowPhaseLiveTag

/-- Every finite delayed tag unconditionally supplies its proof-side common
and literal-child lineage seed. -/
noncomputable def lineageSeed
    (tag : Tag A strategy hwin) :
    ProfiledRawJointHybridShadowPhaseLiveTailLineageSeed A strategy hwin tag := by
  rcases tag with ⟨origin, input, side⟩
  let installed :=
    profiledRawJointHybridShadowPhaseLiveInstalled A strategy hwin origin
  cases side with
  | right =>
      let package := profiledRawJointHybridExactRightPolicy A hwin installed
      let activation :=
        profiledRawJointHybridExactRightActivation A hwin installed
      let childSlot :=
        profiledRawRightChildSlot A (installed.world.procOneSlot A)
          activation.lambda .both [] (input.2, input.1)
      have htarget :
          (profiledRawJointOneSidedNext A installed.incidenceCode
            installed.rawMove
            (profiledRawJointCommonOneRoundStrictRight input)).family.left () =
              some childSlot := by
        have hactive :=
          activation.target_active_slot .both [] (input.2, input.1)
        have hstrict :=
          profiledRawJointHybridExactRightActivation_strictChild A installed
            package activation input
        rw [← hstrict]
        exact hactive
      refine {
        initialSide := .right
        initialRoot := .inl (installed.world.procOneSlot A)
        childRoot := .inr childSlot
        initial_live := ?_
        child_live := ?_ }
      · rfl
      · change
          profiledRawJointHybridCurrentSlots A
              (profiledRawJointHybridPhysicalCompatibleSideAfter .right 1)
              ((profiledRawJointHybridShadowPhaseLiveRightTag A strategy hwin
                origin input).childCode A strategy hwin).1 () =
            some (.inr childSlot)
        rw [profiledRawJointHybridShadowPhaseLiveRightTag_childCode_fst A
          strategy hwin origin input]
        simpa [profiledRawJointHybridCurrentSlots,
          profiledRawJointOneSidedCurrentSlots,
          IndexedLineageSide.other] using htarget
  | left =>
      let package := profiledRawJointHybridExactLeftPolicy A hwin installed
      let activation :=
        profiledRawJointHybridExactLeftActivation A hwin installed
      let childSlot :=
        profiledRawLeftChildSlot A (installed.world.procTwoSlot A)
          activation.lambda .both [] input
      have htarget :
          (profiledRawJointOneSidedNext A installed.incidenceCode
            installed.rawMove
            (profiledRawJointCommonOneRoundStrictLeft input)).family.right () =
              some childSlot := by
        have hactive := activation.target_active_slot .both [] input
        have hstrict :=
          profiledRawJointHybridExactLeftActivation_strictChild A installed
            package activation input
        rw [← hstrict]
        exact hactive
      refine {
        initialSide := .left
        initialRoot := .inr (installed.world.procTwoSlot A)
        childRoot := .inl childSlot
        initial_live := ?_
        child_live := ?_ }
      · rfl
      · change
          profiledRawJointHybridCurrentSlots A
              (profiledRawJointHybridPhysicalCompatibleSideAfter .left 1)
              ((profiledRawJointHybridShadowPhaseLiveLeftTag A strategy hwin
                origin input).childCode A strategy hwin).1 () =
            some (.inl childSlot)
        rw [profiledRawJointHybridShadowPhaseLiveLeftTag_childCode_fst A
          strategy hwin origin input]
        simpa [profiledRawJointHybridCurrentSlots,
          profiledRawJointOneSidedCurrentSlots,
          IndexedLineageSide.other] using htarget

/-- Consume the canonical seed when assembling a root-aligned tail path.
The caller supplies only the actual tail states and their exact transitions;
the initial side and both first roots are fixed proof-side by the tag. -/
noncomputable def rootAlignedPath
    (tag : Tag A strategy hwin)
    (state : Nat → TailState A strategy hwin tag)
    (state_zero : state 0 = (tag.tailCodePolicy A strategy hwin).run [])
    (state_zero_code : (state 0).1.1 = (tag.childCode A strategy hwin).1)
    (rootAt : Nat → ProfiledRawJointThreadRoot A)
    (transition : ∀ n : Nat,
      ProfiledRawJointHybridShadowPhaseLiveTailRootAlignedTransitionAt A
        strategy hwin tag (state n) (state (n + 1))
          (profiledRawJointHybridPhysicalCompatibleSideAfter
            (tag.lineageSeed A strategy hwin).initialSide (n + 2))
          (rootAt n)) :
    ProfiledRawJointHybridShadowPhaseLiveTailRootAlignedPath A strategy hwin
      tag :=
  let seed := tag.lineageSeed A strategy hwin
  { state := state
    state_zero := state_zero
    state_zero_code := state_zero_code
    initialSide := seed.initialSide
    initialRoot := seed.initialRoot
    initial_live := seed.initial_live
    childRoot := seed.childRoot
    child_live := seed.child_live
    rootAt := rootAt
    transition := transition }

end ProfiledRawJointHybridShadowPhaseLiveTag

end

end DetParityAutomaton

end DistributedSynthesis
