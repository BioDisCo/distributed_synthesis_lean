/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveTailTransitionRootAlignment
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridRootPinnedPhysicalPriorityBridge

/-!
# Hidden-lineage alignment along a delayed-tag tail

A delayed tag starts below one literal child of a common root.  Thereafter
every checked physical close supplies a root-aligned exact transition of the
tag's re-rooted tail policy.  This file proves the pure code-lineage fact that
those transition roots are exactly the hidden alternating-lineage states at
times `n + 2`: one step for the literal first child and one for the first tail
transition.

This is proof-side bookkeeping only.  Sides, roots, and path indices are not
added to either local controller.
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

/-- One coherent root-aligned branch below a delayed tag.  The initial common
root and literal child are explicit because the tail policy itself starts at
the child. -/
structure ProfiledRawJointHybridShadowPhaseLiveTailRootAlignedPath
    (tag : Tag A strategy hwin) where
  state : Nat → TailState A strategy hwin tag
  state_zero : state 0 = (tag.tailCodePolicy A strategy hwin).run []
  state_zero_code : (state 0).1.1 = (tag.childCode A strategy hwin).1
  initialSide : IndexedLineageSide
  initialRoot : ProfiledRawJointThreadRoot A
  initial_live :
    let installed :=
      profiledRawJointHybridShadowPhaseLiveInstalled A strategy hwin tag.origin
    let initialCode : ProfiledRawJointHybridCode A :=
      .common ((profiledRawJointCommonWorldFamily A installed.world
        ).incidenceCode A)
    profiledRawJointHybridCurrentSlots A initialSide initialCode () =
      some initialRoot
  childRoot : ProfiledRawJointThreadRoot A
  child_live :
    profiledRawJointHybridCurrentSlots A
        (profiledRawJointHybridPhysicalCompatibleSideAfter initialSide 1)
        (tag.childCode A strategy hwin).1 () =
      some childRoot
  rootAt : Nat → ProfiledRawJointThreadRoot A
  transition : ∀ n : Nat,
    ProfiledRawJointHybridShadowPhaseLiveTailRootAlignedTransitionAt A strategy
      hwin tag (state n) (state (n + 1))
        (profiledRawJointHybridPhysicalCompatibleSideAfter initialSide (n + 2))
        (rootAt n)

namespace ProfiledRawJointHybridShadowPhaseLiveTailRootAlignedPath

/-- The complete bare-code word: literal tagged child, then the positive-time
codes of the re-rooted tail path. -/
noncomputable def codeWord
    {tag : Tag A strategy hwin}
    (path :
      ProfiledRawJointHybridShadowPhaseLiveTailRootAlignedPath A strategy hwin
        tag) : OmegaWord (ProfiledRawJointHybridCode A) :=
  profiledRawJointHybridFirstChildCodeWord A
    (tag.childCode A strategy hwin).1 (fun n ↦ (path.state (n + 1)).1.1)

@[simp] theorem codeWord_zero
    {tag : Tag A strategy hwin}
    (path :
      ProfiledRawJointHybridShadowPhaseLiveTailRootAlignedPath A strategy hwin
        tag) :
    path.codeWord A strategy hwin 0 = (tag.childCode A strategy hwin).1 :=
  rfl

@[simp] theorem codeWord_succ
    {tag : Tag A strategy hwin}
    (path :
      ProfiledRawJointHybridShadowPhaseLiveTailRootAlignedPath A strategy hwin
        tag) (n : Nat) :
    path.codeWord A strategy hwin (n + 1) = (path.state (n + 1)).1.1 :=
  rfl

/-- Every path transition is an allowed edge of the one selected tail
policy. -/
theorem allowed
    {tag : Tag A strategy hwin}
    (path :
      ProfiledRawJointHybridShadowPhaseLiveTailRootAlignedPath A strategy hwin
        tag) (n : Nat) :
    tag.TailAllowedTarget A strategy hwin (path.state n)
      (path.state (n + 1)) :=
  (path.transition n).allowed A strategy hwin

/-- At time `n + 2`, the hidden code-lineage run is live at exactly the root
carried by the `n`th tail transition. -/
theorem lineage_live_at_target
    {tag : Tag A strategy hwin}
    (path :
      ProfiledRawJointHybridShadowPhaseLiveTailRootAlignedPath A strategy hwin
        tag) : ∀ n : Nat,
    let installed :=
      profiledRawJointHybridShadowPhaseLiveInstalled A strategy hwin tag.origin
    let initialCode : ProfiledRawJointHybridCode A :=
      .common ((profiledRawJointCommonWorldFamily A installed.world
        ).incidenceCode A)
    codedAlternatingIndexedLineageCodeRun initialCode
        (profiledRawJointHybridCurrentSlots A)
        (path.codeWord A strategy hwin) path.initialSide () (n + 2) =
      (path.codeWord A strategy hwin (n + 1),
        .live
          (profiledRawJointHybridPhysicalCompatibleSideAfter path.initialSide
            (n + 2))
          () (path.rootAt n)) := by
  intro n
  dsimp only
  let installed :=
    profiledRawJointHybridShadowPhaseLiveInstalled A strategy hwin tag.origin
  let initialCode : ProfiledRawJointHybridCode A :=
    .common ((profiledRawJointCommonWorldFamily A installed.world
      ).incidenceCode A)
  induction n with
  | zero =>
      unfold codedAlternatingIndexedLineageCodeRun
      rw [codedAlternatingIndexedLineageRun_succ]
      rw [codedAlternatingIndexedLineageRun_succ]
      rw [codedAlternatingIndexedLineageRun_zero]
      have hfirst :
          codedAlternatingIndexedLineageStep
              (fun _ (_ : Unit) childCode ↦ childCode)
              (profiledRawJointHybridCurrentSlots A)
              (codedAlternatingIndexedLineageCodeChild
                (profiledRawJointHybridCurrentSlots A))
              (initialCode, .initial)
              ((), path.codeWord A strategy hwin 0)
              (path.initialSide, ()) =
            (path.codeWord A strategy hwin 0,
              .live
                (profiledRawJointHybridPhysicalCompatibleSideAfter
                  path.initialSide 1)
                () path.childRoot) := by
        simpa only [profiledRawJointHybridPhysicalCompatibleSideAfter_succ,
          profiledRawJointHybridPhysicalCompatibleSideAfter_zero] using
          codedAlternatingIndexedLineageCodeStep_initial_of
            (profiledRawJointHybridCurrentSlots A) initialCode
            (path.codeWord A strategy hwin 0) path.initialSide ()
            path.initialRoot path.childRoot path.initial_live path.child_live
      rw [hfirst]
      simpa only [profiledRawJointHybridPhysicalCompatibleSideAfter_succ] using
        codedAlternatingIndexedLineageCodeStep_live_of
          (profiledRawJointHybridCurrentSlots A)
          (path.codeWord A strategy hwin 0)
          (path.codeWord A strategy hwin 1)
          (profiledRawJointHybridPhysicalCompatibleSideAfter path.initialSide 1)
          () path.childRoot (path.rootAt 0) (path.initialSide, ())
          path.child_live (path.transition 0).transition.child_live
  | succ n ih =>
      change
        codedAlternatingIndexedLineageStep
            (fun _ (_ : Unit) childCode ↦ childCode)
            (profiledRawJointHybridCurrentSlots A)
            (codedAlternatingIndexedLineageCodeChild
              (profiledRawJointHybridCurrentSlots A))
            (codedAlternatingIndexedLineageCodeRun initialCode
              (profiledRawJointHybridCurrentSlots A)
              (path.codeWord A strategy hwin) path.initialSide () (n + 2))
            ((), path.codeWord A strategy hwin (n + 2))
            (path.initialSide, ()) = _
      rw [ih]
      simpa only [profiledRawJointHybridPhysicalCompatibleSideAfter_succ] using
        codedAlternatingIndexedLineageCodeStep_live_of
          (profiledRawJointHybridCurrentSlots A)
          (path.codeWord A strategy hwin (n + 1))
          (path.codeWord A strategy hwin (n + 2))
          (profiledRawJointHybridPhysicalCompatibleSideAfter path.initialSide
            (n + 2))
          () (path.rootAt n) (path.rootAt (n + 1))
          (path.initialSide, ())
          (path.transition n).transition.child_live
          (path.transition (n + 1)).transition.child_live

/-- Priority form of `lineage_live_at_target`, ready to rewrite the physical
block-minimum equation in the acceptance certificate. -/
theorem threadPriority_eq_rootPriority
    {tag : Tag A strategy hwin}
    (path :
      ProfiledRawJointHybridShadowPhaseLiveTailRootAlignedPath A strategy hwin
        tag) (n : Nat) :
    let installed :=
      profiledRawJointHybridShadowPhaseLiveInstalled A strategy hwin tag.origin
    let initialCode : ProfiledRawJointHybridCode A :=
      .common ((profiledRawJointCommonWorldFamily A installed.world
        ).incidenceCode A)
    (codedAlternatingIndexedLineageCodeThreadSystem initialCode
        (profiledRawJointHybridCurrentSlots A)
        (profiledRawJointThreadRootPriority A)).priority
      (codedAlternatingIndexedLineageCodeRun initialCode
        (profiledRawJointHybridCurrentSlots A)
        (path.codeWord A strategy hwin) path.initialSide () (n + 2)) =
      profiledRawJointThreadRootPriority A (path.rootAt n) := by
  dsimp only
  rw [path.lineage_live_at_target A strategy hwin n]
  rfl

end ProfiledRawJointHybridShadowPhaseLiveTailRootAlignedPath

end

end DetParityAutomaton

end DistributedSynthesis
