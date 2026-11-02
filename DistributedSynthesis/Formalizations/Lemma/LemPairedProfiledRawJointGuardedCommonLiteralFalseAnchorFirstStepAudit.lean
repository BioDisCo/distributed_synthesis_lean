/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCombinedFreshPhaseLiveCanonicalTwo

/-!
# Generic audit of the false-anchor first table step

The heterogeneous table deliberately fills the unused exact coordinate of
its false member with the default exact receiver output.  This file records,
symbolically and for arbitrary automata, which stage the first synchronized
false-member step therefore installs.  No finite micro-instance or native
evaluation is used.
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

/-! ## The generic information loss -/

/-- The false first-record guard is definitionally insensitive to the second
receiver-output coordinate.  This is the coordinate from which the staged
front later tries to read an exact recurrent child. -/
theorem finiteCrossAnchorHeterogeneousFirstAllowed_false_snd_irrelevant
    {RIn SIn ROut₀ ROut₁ SOut : Type*}
    (falseAllowed : RealizedBlockRound RIn SIn ROut₀ SOut → Bool)
    (trueAllowed : RealizedBlockRound RIn SIn ROut₁ SOut → Bool)
    (record : RealizedBlockRound RIn SIn (ROut₀ × ROut₁) SOut)
    (replacement : ROut₁) :
    finiteCrossAnchorHeterogeneousFirstAllowed falseAllowed trueAllowed false
        (record.1, (record.2.1.1, replacement), record.2.2) =
      finiteCrossAnchorHeterogeneousFirstAllowed falseAllowed trueAllowed false
        record :=
  rfl

namespace ProfiledRawJointGuardedCommonDecoratedPolicyPackage

variable {initial : CommonPoint A strategy}

private abbrev Package :=
  ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy hwin initial
    (CrossValid A strategy hwin)

private abbrev Key (package : Package A strategy hwin
    (initial := initial)) :=
  ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin package

private abbrev LeftKey (package : Package A strategy hwin
    (initial := initial)) :=
  ProfiledRawJointGuardedCommonLiteralLeftSeamKey A strategy hwin package

/-! ## Right seam -/

/-- The tagged child actually read from the product output of one staged
first round.  On the false member this is the *unused second coordinate* of
the heterogeneous output. -/
noncomputable def literalRightSeamStagedFirstRoundChild
    (package : Package A strategy hwin (initial := initial))
    (key : Key A strategy hwin package) (row : PairedEntryRow)
    (anchor : Bool) (input : In₁ × In₂) :
    ProfiledRawJointGuardedCommonLiteralRightSeamTaggedChildCode A strategy
      hwin package :=
  let result := package.literalRightSeamStagedFirstRound A strategy hwin key
    row anchor input
  ⟨key, result.1.1.2.2.target row⟩

/-- Staging itself adds no information: it applies `StageOfChild` to exactly
the product-output child above. -/
theorem literalRightSeamStagedFirstRound_stage_eq_stageOfChild
    (package : Package A strategy hwin (initial := initial))
    (key : Key A strategy hwin package) (row : PairedEntryRow)
    (anchor : Bool) (input : In₁ × In₂) :
    let result := package.literalRightSeamStagedFirstRound A strategy hwin key
      row anchor input
    result.2.1.2.2.2 =
      package.literalRightSeamStageOfChild A strategy hwin row
        (package.literalRightSeamStagedFirstRoundChild A strategy hwin key row
          anchor input) :=
  rfl

/-- `StageOfChild` equals a specified canonical exact stage iff its child is
the specified canonical tagged target.  The forward implication uses the
child field of the stage and is therefore independent of how the finite table
was extracted. -/
theorem literalRightSeamStageOfChild_eq_exact_iff
    (package : Package A strategy hwin (initial := initial))
    (key : Key A strategy hwin package) (row : PairedEntryRow)
    (child :
      ProfiledRawJointGuardedCommonLiteralRightSeamTaggedChildCode A strategy
        hwin package)
    (past : List (In₁ × In₂)) (input : In₁ × In₂) :
    package.literalRightSeamStageOfChild A strategy hwin row child =
        some (package.literalRightSeamExactStage A strategy hwin key row past
          input) ↔
      child = package.literalRightSeamTaggedTarget A strategy hwin key row past
        input := by
  constructor
  · intro hstage
    have hchild := package.literalRightSeamStageOfChild_child A strategy hwin
      row child
      (package.literalRightSeamExactStage A strategy hwin key row past input)
      hstage
    exact hchild.symm
  · intro hchild
    subst child
    exact package.literalRightSeamStageOfChild_exact A strategy hwin key row
      past input

/-- Kernel-level verdict for the false anchor.  The desired current-record
stage is equivalent to a target equality for the unused second product
coordinate.  The false-member monitor and its first-record guard project only
`Prod.fst`, so the existing table interface supplies no premise capable of
closing this equality. -/
theorem literalRightSeamStagedFirstRound_false_stage_eq_exact_iff
    (package : Package A strategy hwin (initial := initial))
    (key : Key A strategy hwin package) (row : PairedEntryRow)
    (input : In₁ × In₂) :
    let result := package.literalRightSeamStagedFirstRound A strategy hwin key
      row false input
    result.2.1.2.2.2 =
        some (package.literalRightSeamExactStage A strategy hwin key row []
          input) ↔
      package.literalRightSeamStagedFirstRoundChild A strategy hwin key row
          false input =
        package.literalRightSeamTaggedTarget A strategy hwin key row []
          input := by
  dsimp only
  rw [package.literalRightSeamStagedFirstRound_stage_eq_stageOfChild A
    strategy hwin]
  exact package.literalRightSeamStageOfChild_eq_exact_iff A strategy hwin key
    row _ [] input

/-! ## Left seam mirror -/

noncomputable def literalLeftSeamStagedFirstRoundChild
    (package : Package A strategy hwin (initial := initial))
    (key : LeftKey A strategy hwin package) (row : PairedEntryRow)
    (anchor : Bool) (input : In₂ × In₁) :
    ProfiledRawJointGuardedCommonLiteralLeftSeamTaggedChildCode A strategy hwin
      package :=
  let result := package.literalLeftSeamStagedFirstRound A strategy hwin key row
    anchor input
  ⟨key, result.1.1.2.2.target row⟩

theorem literalLeftSeamStagedFirstRound_stage_eq_stageOfChild
    (package : Package A strategy hwin (initial := initial))
    (key : LeftKey A strategy hwin package) (row : PairedEntryRow)
    (anchor : Bool) (input : In₂ × In₁) :
    let result := package.literalLeftSeamStagedFirstRound A strategy hwin key
      row anchor input
    result.2.1.2.2.2 =
      package.literalLeftSeamStageOfChild A strategy hwin row
        (package.literalLeftSeamStagedFirstRoundChild A strategy hwin key row
          anchor input) :=
  rfl

theorem literalLeftSeamStageOfChild_eq_exact_iff
    (package : Package A strategy hwin (initial := initial))
    (key : LeftKey A strategy hwin package) (row : PairedEntryRow)
    (child :
      ProfiledRawJointGuardedCommonLiteralLeftSeamTaggedChildCode A strategy
        hwin package)
    (past : List (In₂ × In₁)) (input : In₂ × In₁) :
    package.literalLeftSeamStageOfChild A strategy hwin row child =
        some (package.literalLeftSeamExactStage A strategy hwin key row past
          input) ↔
      child = package.literalLeftSeamTaggedTarget A strategy hwin key row past
        input := by
  constructor
  · intro hstage
    have hchild := package.literalLeftSeamStageOfChild_child A strategy hwin
      row child
      (package.literalLeftSeamExactStage A strategy hwin key row past input)
      hstage
    exact hchild.symm
  · intro hchild
    subst child
    exact package.literalLeftSeamStageOfChild_exact A strategy hwin key row
      past input

theorem literalLeftSeamStagedFirstRound_false_stage_eq_exact_iff
    (package : Package A strategy hwin (initial := initial))
    (key : LeftKey A strategy hwin package) (row : PairedEntryRow)
    (input : In₂ × In₁) :
    let result := package.literalLeftSeamStagedFirstRound A strategy hwin key
      row false input
    result.2.1.2.2.2 =
        some (package.literalLeftSeamExactStage A strategy hwin key row []
          input) ↔
      package.literalLeftSeamStagedFirstRoundChild A strategy hwin key row
          false input =
        package.literalLeftSeamTaggedTarget A strategy hwin key row []
          input := by
  dsimp only
  rw [package.literalLeftSeamStagedFirstRound_stage_eq_stageOfChild A strategy
    hwin]
  exact package.literalLeftSeamStageOfChild_eq_exact_iff A strategy hwin key
    row _ [] input

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
