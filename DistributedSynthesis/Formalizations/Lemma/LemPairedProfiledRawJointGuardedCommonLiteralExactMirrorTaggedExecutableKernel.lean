/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralExactMirrorTaggedController
import DistributedSynthesis.Formalizations.Lemma.LemFinitePairedMealyController

/-!
# Executable recurrent controller below the exact mirror seam tag

The mirror seam stores the full dependent literal child emitted by its exact
root-pinned right block.  This module totalizes the unused finite front modes
with `Unit` and exposes the indexed recurrent kernel as a standalone finite
paired Mealy controller.  Honest entry is the exact matched-left pair selected
by the checked seam target.

The `Unit` branches are unreachable after this entry.  Every live transition
is an existing indexed-policy transition, and executable maps receive only
finite local controls and locally available inputs—never a graph,
orientation, hierarchy side, leader bit, semantic history, or view.
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

private abbrev Package (initial : CommonPoint A strategy) :=
  ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy hwin initial
    (CrossValid A strategy hwin)

private abbrev TaggedChild (initial : CommonPoint A strategy)
    (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralLeftSeamTaggedChildCode A strategy hwin
    package

/-- Process-one finite control below all exact mirror seam tags. -/
abbrev ProfiledRawJointGuardedCommonLiteralLeftSeamOneControl
    (package : Package A strategy hwin initial) :=
  ProfiledRawJointLeaderFreeOneControl Unit Unit
    (TaggedChild A strategy hwin initial package)
    (ProfiledRawJointGuardedCommonLiteralLeftSeamTaggedRightOwner A strategy
      hwin package)
    (ProfiledRawJointGuardedCommonLiteralLeftSeamTaggedLeftReceiver A strategy
      hwin package)

/-- Process-two finite mirror control. -/
abbrev ProfiledRawJointGuardedCommonLiteralLeftSeamTwoControl
    (package : Package A strategy hwin initial) :=
  ProfiledRawJointLeaderFreeTwoControl Unit Unit
    (TaggedChild A strategy hwin initial package)
    (ProfiledRawJointGuardedCommonLiteralLeftSeamTaggedRightReceiver A strategy
      hwin package)
    (ProfiledRawJointGuardedCommonLiteralLeftSeamTaggedLeftOwner A strategy hwin
      package)

noncomputable instance literalLeftSeamOneControlFintype
    (package : Package A strategy hwin initial) :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralLeftSeamOneControl A strategy hwin
        package) := by
  classical
  infer_instance

noncomputable instance literalLeftSeamTwoControlFintype
    (package : Package A strategy hwin initial) :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralLeftSeamTwoControl A strategy hwin
        package) := by
  classical
  infer_instance

/-- Harmless totalization of front constructors which are unreachable after
entry through `literalLeftSeamTaggedMatched`. -/
noncomputable def literalLeftSeamTaggedUnitAdapter
    (package : Package A strategy hwin initial) :
    ProfiledRawJointGuardedCommonLiteralLeftSeamExceptionalAdapter A strategy
      hwin package Unit Unit Unit Unit where
  initialOne := ()
  initialTwo := ()
  initialOutputOne := default
  initialOutputTwo := default
  initialNoRecvOne := fun _ _ ↦ (default, .initial ())
  exceptionalNoRecvOne := fun _ _ ↦ (default, .initial ())
  initialNoRecvTwo := fun _ _ ↦ (default, .initial ())
  exceptionalNoRecvTwo := fun _ _ ↦ (default, .initial ())
  otherRecvOne := fun _ _ _ _ ↦ (default, .initial ())
  otherRecvTwo := fun _ _ _ _ ↦ (default, .initial ())

/-- Complete executable indexed recurrent kernel below the mirror tag. -/
noncomputable def literalLeftSeamTaggedExecutableKernel
    (package : Package A strategy hwin initial) :=
  package.literalLeftSeamTaggedLeaderFreeKernel A strategy hwin
    (package.literalLeftSeamTaggedUnitAdapter A strategy hwin)

/-- Exact matched-left local controls selected by one checked seam target. -/
noncomputable def literalLeftSeamTaggedMatched
    (package : Package A strategy hwin initial)
    (key : ProfiledRawJointGuardedCommonLiteralLeftSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (input : In₂ × In₁) :
    ProfiledRawJointGuardedCommonLiteralLeftSeamOneControl A strategy hwin
        package ×
      ProfiledRawJointGuardedCommonLiteralLeftSeamTwoControl A strategy hwin
        package :=
  let matched := package.literalLeftSeamTaggedTargetInitialMatchedLeft A
    strategy hwin key row past input
  (.leftReceiver matched.1 matched.2.1,
    .leftOwner matched.1 matched.2.2)

@[simp] theorem literalLeftSeamTaggedMatched_one
    (package : Package A strategy hwin initial)
    (key : ProfiledRawJointGuardedCommonLiteralLeftSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (input : In₂ × In₁) :
    (package.literalLeftSeamTaggedMatched A strategy hwin key row past
      input).1 =
      .leftReceiver
        (package.literalLeftSeamTaggedTarget A strategy hwin key row past input)
        (package.literalLeftSeamTaggedTargetInitialLeftReceiver A strategy hwin
          key row past input) :=
  rfl

@[simp] theorem literalLeftSeamTaggedMatched_two
    (package : Package A strategy hwin initial)
    (key : ProfiledRawJointGuardedCommonLiteralLeftSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (input : In₂ × In₁) :
    (package.literalLeftSeamTaggedMatched A strategy hwin key row past
      input).2 =
      .leftOwner
        (package.literalLeftSeamTaggedTarget A strategy hwin key row past input)
        (package.literalLeftSeamTaggedTargetInitialLeftOwner A strategy hwin key
          row past input) :=
  rfl

/-! ## State-first Mealy maps -/

noncomputable def literalLeftSeamTaggedNoRecvOne
    (package : Package A strategy hwin initial)
    (state : ProfiledRawJointGuardedCommonLiteralLeftSeamOneControl A strategy
      hwin package) (input : In₁) :
    ProfiledRawJointGuardedCommonLiteralLeftSeamOneControl A strategy hwin
        package × Out₁ :=
  let next :=
    (package.literalLeftSeamTaggedExecutableKernel A strategy hwin).noRecvOne
      state input
  (next.2, next.1)

noncomputable def literalLeftSeamTaggedNoRecvTwo
    (package : Package A strategy hwin initial)
    (state : ProfiledRawJointGuardedCommonLiteralLeftSeamTwoControl A strategy
      hwin package) (input : In₂) :
    ProfiledRawJointGuardedCommonLiteralLeftSeamTwoControl A strategy hwin
        package × Out₂ :=
  let next :=
    (package.literalLeftSeamTaggedExecutableKernel A strategy hwin).noRecvTwo
      state input
  (next.2, next.1)

noncomputable def literalLeftSeamTaggedRecvOne
    (package : Package A strategy hwin initial)
    (one : ProfiledRawJointGuardedCommonLiteralLeftSeamOneControl A strategy
      hwin package) (own : In₁)
    (two : ProfiledRawJointGuardedCommonLiteralLeftSeamTwoControl A strategy
      hwin package) (delivered : In₂) :
    ProfiledRawJointGuardedCommonLiteralLeftSeamOneControl A strategy hwin
        package × Out₁ :=
  let next :=
    (package.literalLeftSeamTaggedExecutableKernel A strategy hwin).recvOne one
      own two delivered
  (next.2, next.1)

noncomputable def literalLeftSeamTaggedRecvTwo
    (package : Package A strategy hwin initial)
    (two : ProfiledRawJointGuardedCommonLiteralLeftSeamTwoControl A strategy
      hwin package) (own : In₂)
    (one : ProfiledRawJointGuardedCommonLiteralLeftSeamOneControl A strategy
      hwin package) (delivered : In₁) :
    ProfiledRawJointGuardedCommonLiteralLeftSeamTwoControl A strategy hwin
        package × Out₂ :=
  let next :=
    (package.literalLeftSeamTaggedExecutableKernel A strategy hwin).recvTwo two
      own one delivered
  (next.2, next.1)

/-- Standalone finite paired Mealy controller initialized at the exact
matched-left seam target. -/
noncomputable def literalLeftSeamTaggedRecurrentController
    (package : Package A strategy hwin initial)
    (key : ProfiledRawJointGuardedCommonLiteralLeftSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (input : In₂ × In₁) :
    FinitePairedMealyController In₁ In₂ Out₁ Out₂ where
  OneControl :=
    ProfiledRawJointGuardedCommonLiteralLeftSeamOneControl A strategy hwin
      package
  TwoControl :=
    ProfiledRawJointGuardedCommonLiteralLeftSeamTwoControl A strategy hwin
      package
  oneFinite := inferInstance
  twoFinite := inferInstance
  initialOne :=
    (package.literalLeftSeamTaggedMatched A strategy hwin key row past input).1
  initialTwo :=
    (package.literalLeftSeamTaggedMatched A strategy hwin key row past input).2
  noRecvOne := package.literalLeftSeamTaggedNoRecvOne A strategy hwin
  noRecvTwo := package.literalLeftSeamTaggedNoRecvTwo A strategy hwin
  recvOne := package.literalLeftSeamTaggedRecvOne A strategy hwin
  recvTwo := package.literalLeftSeamTaggedRecvTwo A strategy hwin

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
