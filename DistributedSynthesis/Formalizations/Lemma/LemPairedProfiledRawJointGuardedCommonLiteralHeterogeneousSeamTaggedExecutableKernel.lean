/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralHeterogeneousSeamTaggedController
import DistributedSynthesis.Formalizations.Lemma.LemFinitePairedMealyController

/-!
# Executable recurrent controller below an exact literal seam tag

The exact heterogeneous seam stores the full dependent literal child, and
the tagged controller module supplies the four ordinary recurrent endpoint
families below that child.  This file closes the small totalization boundary
of the indexed leader-free kernel and exposes an actual finite paired Mealy
controller whose initial controls are the matched right owner/receiver pair
selected by the seam.

The `Unit` initial and exceptional branches below only totalize constructors
which are unreachable after entering through `literalRightSeamTaggedMatched`.
Every recurrent transition is the already checked indexed-policy transition.
No executable map receives a graph, orientation, hierarchy side, leader bit,
semantic history, or view.
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
  ProfiledRawJointGuardedCommonLiteralRightSeamTaggedChildCode A strategy hwin
    package

/-- Process-one controls of the finite recurrent carrier below all exact seam
tags.  The two `Unit` constructors only totalize unreachable front modes. -/
abbrev ProfiledRawJointGuardedCommonLiteralRightSeamOneControl
    (package : Package A strategy hwin initial) :=
  ProfiledRawJointLeaderFreeOneControl Unit Unit
    (TaggedChild A strategy hwin initial package)
    (ProfiledRawJointGuardedCommonLiteralRightSeamTaggedRightOwner A strategy
      hwin package)
    (ProfiledRawJointGuardedCommonLiteralRightSeamTaggedLeftReceiver A strategy
      hwin package)

/-- Process-two mirror control. -/
abbrev ProfiledRawJointGuardedCommonLiteralRightSeamTwoControl
    (package : Package A strategy hwin initial) :=
  ProfiledRawJointLeaderFreeTwoControl Unit Unit
    (TaggedChild A strategy hwin initial package)
    (ProfiledRawJointGuardedCommonLiteralRightSeamTaggedRightReceiver A
      strategy hwin package)
    (ProfiledRawJointGuardedCommonLiteralRightSeamTaggedLeftOwner A strategy
      hwin package)

noncomputable instance literalRightSeamOneControlFintype
    (package : Package A strategy hwin initial) :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralRightSeamOneControl A strategy hwin
        package) := by
  classical
  infer_instance

noncomputable instance literalRightSeamTwoControlFintype
    (package : Package A strategy hwin initial) :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralRightSeamTwoControl A strategy hwin
        package) := by
  classical
  infer_instance

/-- Harmless totalization of the front constructors.  Honest seam entry uses
neither `initial` nor `exceptional`; it enters a matched recurrent pair. -/
noncomputable def literalRightSeamTaggedUnitAdapter
    (package : Package A strategy hwin initial) :
    ProfiledRawJointGuardedCommonLiteralRightSeamExceptionalAdapter A strategy
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

/-- The complete finite recurrent kernel below the exact tagged family. -/
noncomputable def literalRightSeamTaggedExecutableKernel
    (package : Package A strategy hwin initial) :=
  package.literalRightSeamTaggedLeaderFreeKernel A strategy hwin
    (package.literalRightSeamTaggedUnitAdapter A strategy hwin)

/-- Exact joint matched-right controls selected by one checked seam target. -/
noncomputable def literalRightSeamTaggedMatched
    (package : Package A strategy hwin initial)
    (key : ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂) :
    ProfiledRawJointGuardedCommonLiteralRightSeamOneControl A strategy hwin
        package ×
      ProfiledRawJointGuardedCommonLiteralRightSeamTwoControl A strategy hwin
        package :=
  let matched := package.literalRightSeamTaggedTargetInitialMatchedRight A
    strategy hwin key row past input
  (.rightOwner matched.1 matched.2.1,
    .rightReceiver matched.1 matched.2.2)

@[simp] theorem literalRightSeamTaggedMatched_one
    (package : Package A strategy hwin initial)
    (key : ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂) :
    (package.literalRightSeamTaggedMatched A strategy hwin key row past
      input).1 =
      .rightOwner
        (package.literalRightSeamTaggedTarget A strategy hwin key row past
          input)
        (package.literalRightSeamTaggedTargetInitialRightOwner A strategy hwin
          key row past input) :=
  rfl

@[simp] theorem literalRightSeamTaggedMatched_two
    (package : Package A strategy hwin initial)
    (key : ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂) :
    (package.literalRightSeamTaggedMatched A strategy hwin key row past
      input).2 =
      .rightReceiver
        (package.literalRightSeamTaggedTarget A strategy hwin key row past
          input)
        (package.literalRightSeamTaggedTargetInitialRightReceiver A strategy
          hwin key row past input) :=
  rfl

/-! ## State-first Mealy maps -/

noncomputable def literalRightSeamTaggedNoRecvOne
    (package : Package A strategy hwin initial)
    (state : ProfiledRawJointGuardedCommonLiteralRightSeamOneControl A
      strategy hwin package) (input : In₁) :
    ProfiledRawJointGuardedCommonLiteralRightSeamOneControl A strategy hwin
        package × Out₁ :=
  let next :=
    (package.literalRightSeamTaggedExecutableKernel A strategy hwin).noRecvOne
      state input
  (next.2, next.1)

noncomputable def literalRightSeamTaggedNoRecvTwo
    (package : Package A strategy hwin initial)
    (state : ProfiledRawJointGuardedCommonLiteralRightSeamTwoControl A
      strategy hwin package) (input : In₂) :
    ProfiledRawJointGuardedCommonLiteralRightSeamTwoControl A strategy hwin
        package × Out₂ :=
  let next :=
    (package.literalRightSeamTaggedExecutableKernel A strategy hwin).noRecvTwo
      state input
  (next.2, next.1)

noncomputable def literalRightSeamTaggedRecvOne
    (package : Package A strategy hwin initial)
    (one : ProfiledRawJointGuardedCommonLiteralRightSeamOneControl A strategy
      hwin package) (own : In₁)
    (two : ProfiledRawJointGuardedCommonLiteralRightSeamTwoControl A strategy
      hwin package) (delivered : In₂) :
    ProfiledRawJointGuardedCommonLiteralRightSeamOneControl A strategy hwin
        package × Out₁ :=
  let next :=
    (package.literalRightSeamTaggedExecutableKernel A strategy hwin).recvOne
      one own two delivered
  (next.2, next.1)

noncomputable def literalRightSeamTaggedRecvTwo
    (package : Package A strategy hwin initial)
    (two : ProfiledRawJointGuardedCommonLiteralRightSeamTwoControl A strategy
      hwin package) (own : In₂)
    (one : ProfiledRawJointGuardedCommonLiteralRightSeamOneControl A strategy
      hwin package) (delivered : In₁) :
    ProfiledRawJointGuardedCommonLiteralRightSeamTwoControl A strategy hwin
        package × Out₂ :=
  let next :=
    (package.literalRightSeamTaggedExecutableKernel A strategy hwin).recvTwo
      two own one delivered
  (next.2, next.1)

/-- A standalone finite paired controller below one exact seam target.  Its
parameters are fixed construction data; its executable transitions use only
local controls and actually available inputs. -/
noncomputable def literalRightSeamTaggedRecurrentController
    (package : Package A strategy hwin initial)
    (key : ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂) :
    FinitePairedMealyController In₁ In₂ Out₁ Out₂ where
  OneControl :=
    ProfiledRawJointGuardedCommonLiteralRightSeamOneControl A strategy hwin
      package
  TwoControl :=
    ProfiledRawJointGuardedCommonLiteralRightSeamTwoControl A strategy hwin
      package
  oneFinite := inferInstance
  twoFinite := inferInstance
  initialOne :=
    (package.literalRightSeamTaggedMatched A strategy hwin key row past
      input).1
  initialTwo :=
    (package.literalRightSeamTaggedMatched A strategy hwin key row past
      input).2
  noRecvOne := package.literalRightSeamTaggedNoRecvOne A strategy hwin
  noRecvTwo := package.literalRightSeamTaggedNoRecvTwo A strategy hwin
  recvOne := package.literalRightSeamTaggedRecvOne A strategy hwin
  recvTwo := package.literalRightSeamTaggedRecvTwo A strategy hwin

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
