/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralHeterogeneousSeamTaggedStagedFront
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralExactMirrorTaggedStagedFront
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointUnitFixedTailSoundness

/-!
# Fixed-tail acceptance of a live literal seam stage

A live heterogeneous-seam stage already contains a reachable macro of the
ordinary one-sided policy.  The controller bank was proved sound at every
such macro, not only at the root of the policy.  Consequently the stage can
be handed directly to the existing fixed-side theorem: no suffix
rationalization and no observable hierarchy-side bit are required.

This file records that small adapter in both orientations.  The companion
`...StagedReversal_exact_pair` theorems identify the first executable
reversal step with the matched ordinary owner/receiver pair, while the
theorems below supply the infinite acceptance fact at the very same macro.
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

/-! ## Right stage -/

private abbrev RightStage
    (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralRightSeamStage A strategy hwin package

/-- The physical paired lambda installed by an arbitrary live right stage.
Its source macro is reachable by construction of the stage. -/
noncomputable def literalRightSeamStageLambda
    (package : Package A strategy hwin initial)
    (stage : RightStage A strategy hwin package) :
    ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) :=
  let source :=
    package.literalRightSeamTaggedChildSource A strategy hwin stage.child
  let policy :=
    package.literalRightSeamTaggedChildPolicy A strategy hwin stage.child
  let bank :=
    package.literalRightSeamTaggedChildControllerBank A strategy hwin
      stage.child
  profiledRawJointUnitRightLambdaOfNarrowed A strategy (source.code A) policy
    stage.root.state stage.root.slot
    ((bank.right stage.root).1).labeledTree

/-- Every live right stage, including one refreshed at an arbitrary later
table record, installs a fixed-right controller satisfying both latent entry
rows. -/
theorem literalRightSeamStage_forever
    (package : Package A strategy hwin initial)
    (stage : RightStage A strategy hwin package) :
    PairedRightForeverAccepts A stage.root.slot.1.1
      (package.literalRightSeamStageLambda A strategy hwin stage) := by
  let bank :=
    package.literalRightSeamTaggedChildControllerBank A strategy hwin
      stage.child
  simpa [literalRightSeamStageLambda, bank] using
    (bank.right_forever A stage.root)

/-- In particular, every exact record-relative stage produced by the true
table member has the fixed-right acceptance guarantee. -/
theorem literalRightSeamExactStage_forever
    (package : Package A strategy hwin initial)
    (key : ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂) :
    let stage := package.literalRightSeamExactStage A strategy hwin key row
      past input
    PairedRightForeverAccepts A stage.root.slot.1.1
      (package.literalRightSeamStageLambda A strategy hwin stage) := by
  dsimp only
  exact package.literalRightSeamStage_forever A strategy hwin _

/-- Row-wise physical acceptance of the fresh strict-right tail selected by
an arbitrary stage.  This is the direct form consumed by a physical trace
handoff. -/
theorem literalRightSeamStage_physical_acceptsFrom
    (package : Package A strategy hwin initial)
    (stage : RightStage A strategy hwin package)
    (row : PairedEntryRow) (env : Nat → In₂ × In₁) :
    let bank :=
      package.literalRightSeamTaggedChildControllerBank A strategy hwin
        stage.child
    A.AcceptsFrom
      (match row with
      | .first => stage.root.slot.1.1.1
      | .both => stage.root.slot.1.1.2)
      (fun n ↦ pairedRightRecordForRow row
        (profiledRawJointUnitRightPhysicalLetter A
          (profiledRawJointUnitRightPolicyOmegaPlay A bank stage.root env n))) :=
  by
    dsimp only
    exact
      (package.literalRightSeamTaggedChildControllerBank A strategy hwin
        stage.child).right_physical_acceptsFrom A stage.root row env

/-- Operational handoff in one statement: the two local reversal maps take
the first step of one matched ordinary controller, and that controller has
the fixed-right acceptance guarantee. -/
theorem literalRightSeamStagedReversal_exact_pair_and_forever
    (package : Package A strategy hwin initial)
    (receiver :
      ProfiledRawJointGuardedCommonLiteralRightSeamStagedReceiverState A
        strategy hwin package)
    (sender :
      ProfiledRawJointGuardedCommonLiteralRightSeamStagedSenderState A strategy
        hwin package)
    (stage : RightStage A strategy hwin package)
    (hstage : receiver.2.2.2 = some stage)
    (input : In₁ × In₂) :
    let matched := package.literalRightSeamStageMatched A strategy hwin stage
    package.literalRightSeamStagedReversalNoRecvOne A strategy hwin receiver
          input.1 =
        ((package.literalRightSeamTaggedNoRecvOne A strategy hwin matched.1
          input.1).2,
          (package.literalRightSeamTaggedNoRecvOne A strategy hwin matched.1
            input.1).1) ∧
      package.literalRightSeamStagedReversalRecvTwo A strategy hwin sender
          input.2 receiver input.1 =
        ((package.literalRightSeamTaggedRecvTwo A strategy hwin matched.2
          input.2 matched.1 input.1).2,
          (package.literalRightSeamTaggedRecvTwo A strategy hwin matched.2
            input.2 matched.1 input.1).1) ∧
      PairedRightForeverAccepts A stage.root.slot.1.1
        (package.literalRightSeamStageLambda A strategy hwin stage) := by
  dsimp only
  have hpair := package.literalRightSeamStagedReversal_exact_pair A strategy
    hwin receiver sender stage hstage input
  exact ⟨hpair.1, hpair.2,
    package.literalRightSeamStage_forever A strategy hwin stage⟩

/-! ## Left mirror stage -/

private abbrev LeftStage
    (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralLeftSeamStage A strategy hwin package

/-- Physical paired lambda installed by an arbitrary live mirror stage. -/
noncomputable def literalLeftSeamStageLambda
    (package : Package A strategy hwin initial)
    (stage : LeftStage A strategy hwin package) :
    ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) :=
  let source :=
    package.literalLeftSeamTaggedChildSource A strategy hwin stage.child
  let policy :=
    package.literalLeftSeamTaggedChildPolicy A strategy hwin stage.child
  let bank :=
    package.literalLeftSeamTaggedChildControllerBank A strategy hwin
      stage.child
  profiledRawJointUnitLeftLambdaOfNarrowed A strategy (source.code A) policy
    stage.root.state stage.root.slot
    ((bank.left stage.root).1).labeledTree

/-- Every live mirror stage installs a fixed-left controller satisfying both
latent entry rows. -/
theorem literalLeftSeamStage_forever
    (package : Package A strategy hwin initial)
    (stage : LeftStage A strategy hwin package) :
    PairedLeftForeverAccepts A stage.root.slot.1.1
      (package.literalLeftSeamStageLambda A strategy hwin stage) := by
  let bank :=
    package.literalLeftSeamTaggedChildControllerBank A strategy hwin
      stage.child
  simpa [literalLeftSeamStageLambda, bank] using
    (bank.left_forever A stage.root)

/-- Exact record-relative mirror stages inherit fixed-left acceptance. -/
theorem literalLeftSeamExactStage_forever
    (package : Package A strategy hwin initial)
    (key : ProfiledRawJointGuardedCommonLiteralLeftSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (input : In₂ × In₁) :
    let stage := package.literalLeftSeamExactStage A strategy hwin key row past
      input
    PairedLeftForeverAccepts A stage.root.slot.1.1
      (package.literalLeftSeamStageLambda A strategy hwin stage) := by
  dsimp only
  exact package.literalLeftSeamStage_forever A strategy hwin _

/-- Row-wise physical acceptance of the strict-left tail selected by an
arbitrary live mirror stage. -/
theorem literalLeftSeamStage_physical_acceptsFrom
    (package : Package A strategy hwin initial)
    (stage : LeftStage A strategy hwin package)
    (row : PairedEntryRow) (env : Nat → In₁ × In₂) :
    let bank :=
      package.literalLeftSeamTaggedChildControllerBank A strategy hwin
        stage.child
    A.AcceptsFrom
      (match row with
      | .first => stage.root.slot.1.1.1
      | .both => stage.root.slot.1.1.2)
      (fun n ↦ pairedLeftRecordForRow row
        (profiledRawJointUnitLeftPhysicalLetter A
          (profiledRawJointUnitLeftPolicyOmegaPlay A bank stage.root env n))) :=
  by
    dsimp only
    exact
      (package.literalLeftSeamTaggedChildControllerBank A strategy hwin
        stage.child).left_physical_acceptsFrom A stage.root row env

/-- Mirror operational handoff: the executable reversal step and the
fixed-left acceptance proof refer to the very same retained stage. -/
theorem literalLeftSeamStagedReversal_exact_pair_and_forever
    (package : Package A strategy hwin initial)
    (receiver :
      ProfiledRawJointGuardedCommonLiteralLeftSeamStagedReceiverState A
        strategy hwin package)
    (sender :
      ProfiledRawJointGuardedCommonLiteralLeftSeamStagedSenderState A strategy
        hwin package)
    (stage : LeftStage A strategy hwin package)
    (hstage : receiver.2.2.2 = some stage)
    (input : In₁ × In₂) :
    let matched := package.literalLeftSeamStageMatched A strategy hwin stage
    package.literalLeftSeamStagedReversalRecvOne A strategy hwin sender
          input.1 receiver input.2 =
        ((package.literalLeftSeamTaggedRecvOne A strategy hwin matched.1
          input.1 matched.2 input.2).2,
          (package.literalLeftSeamTaggedRecvOne A strategy hwin matched.1
            input.1 matched.2 input.2).1) ∧
      package.literalLeftSeamStagedReversalNoRecvTwo A strategy hwin receiver
          input.2 =
        ((package.literalLeftSeamTaggedNoRecvTwo A strategy hwin matched.2
          input.2).2,
          (package.literalLeftSeamTaggedNoRecvTwo A strategy hwin matched.2
            input.2).1) ∧
      PairedLeftForeverAccepts A stage.root.slot.1.1
        (package.literalLeftSeamStageLambda A strategy hwin stage) := by
  dsimp only
  have hpair := package.literalLeftSeamStagedReversal_exact_pair A strategy
    hwin receiver sender stage hstage input
  exact ⟨hpair.1, hpair.2,
    package.literalLeftSeamStage_forever A strategy hwin stage⟩

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
