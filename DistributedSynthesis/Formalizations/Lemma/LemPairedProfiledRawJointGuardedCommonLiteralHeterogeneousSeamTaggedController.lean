/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralHeterogeneousSeamTaggedFamily
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralExactTailHandoff
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointIndexedPolicyLeaderFreeKernel

/-!
# Finite recurrent carriers below an exact guarded-common seam tag

The heterogeneous seam tag retains the full dependent literal child selected
by one root-pinned first block.  This file equips every such tag with the four
finite endpoint carrier families of its exact ordinary policy.  Hence a
resolved seam can enter a recurrent controller without replacing the child by
another representative having only the same incidence code.

All dependence on the semantic occurrence is frozen in the finite tag family.
The executable carrier states contain only the tag and finite controller
states; they receive no graph, orientation, leader bit, history, or view.
-/

namespace DistributedSynthesis

universe u v x y s i₁ i₂ e₁ e₂

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

/-! ## The exact recurrent bank selected by a seam tag -/

/-- Complete ordinary recurrent controller bank below the exact tagged
literal child. -/
noncomputable def literalRightSeamTaggedChildControllerBank
    (package : Package A strategy hwin initial)
    (child : TaggedChild A strategy hwin initial package) :
    ProfiledRawJointUnitPolicyControllerBank A strategy
      (package.literalRightSeamTaggedChildSource A strategy hwin child)
      (package.literalRightSeamTaggedChildPolicy A strategy hwin child) :=
  profiledRawJointUnitPolicyControllerBank A strategy
    (package.literalRightSeamTaggedChildSource A strategy hwin child)
    (package.literalRightSeamTaggedChildPolicy A strategy hwin child)

/-! ## Four finite dependent endpoint families -/

/-- Process one is the owner of the right-policy continuation. -/
abbrev ProfiledRawJointGuardedCommonLiteralRightSeamTaggedRightOwner
    (package : Package A strategy hwin initial)
    (child : TaggedChild A strategy hwin initial package) :=
  ProfiledRawJointUnitPolicyRightOwner A strategy
    (package.literalRightSeamTaggedChildSource A strategy hwin child)
    (package.literalRightSeamTaggedChildPolicy A strategy hwin child)
    (package.literalRightSeamTaggedChildControllerBank A strategy hwin child)
    ()

/-- Process two is the matching right-policy receiver. -/
abbrev ProfiledRawJointGuardedCommonLiteralRightSeamTaggedRightReceiver
    (package : Package A strategy hwin initial)
    (child : TaggedChild A strategy hwin initial package) :=
  ProfiledRawJointUnitPolicyRightReceiver A strategy
    (package.literalRightSeamTaggedChildSource A strategy hwin child)
    (package.literalRightSeamTaggedChildPolicy A strategy hwin child) ()

/-- Left-policy owner family, included for later strict reversals. -/
abbrev ProfiledRawJointGuardedCommonLiteralRightSeamTaggedLeftOwner
    (package : Package A strategy hwin initial)
    (child : TaggedChild A strategy hwin initial package) :=
  ProfiledRawJointUnitPolicyLeftOwner A strategy
    (package.literalRightSeamTaggedChildSource A strategy hwin child)
    (package.literalRightSeamTaggedChildPolicy A strategy hwin child)
    (package.literalRightSeamTaggedChildControllerBank A strategy hwin child)
    ()

/-- Matching left-policy receiver family. -/
abbrev ProfiledRawJointGuardedCommonLiteralRightSeamTaggedLeftReceiver
    (package : Package A strategy hwin initial)
    (child : TaggedChild A strategy hwin initial package) :=
  ProfiledRawJointUnitPolicyLeftReceiver A strategy
    (package.literalRightSeamTaggedChildSource A strategy hwin child)
    (package.literalRightSeamTaggedChildPolicy A strategy hwin child) ()

noncomputable instance literalRightSeamTaggedRightOwnerFintype
    (package : Package A strategy hwin initial)
    (child : TaggedChild A strategy hwin initial package) :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralRightSeamTaggedRightOwner A
        strategy hwin package child) := by
  classical
  infer_instance

noncomputable instance literalRightSeamTaggedRightReceiverFintype
    (package : Package A strategy hwin initial)
    (child : TaggedChild A strategy hwin initial package) :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralRightSeamTaggedRightReceiver A
        strategy hwin package child) := by
  classical
  infer_instance

noncomputable instance literalRightSeamTaggedLeftOwnerFintype
    (package : Package A strategy hwin initial)
    (child : TaggedChild A strategy hwin initial package) :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralRightSeamTaggedLeftOwner A strategy
        hwin package child) := by
  classical
  infer_instance

noncomputable instance literalRightSeamTaggedLeftReceiverFintype
    (package : Package A strategy hwin initial)
    (child : TaggedChild A strategy hwin initial package) :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralRightSeamTaggedLeftReceiver A
        strategy hwin package child) := by
  classical
  infer_instance

/-! ## Uniform finite sums used by executable endpoint controls -/

/-- All right-policy owner states below all finite seam tags. -/
abbrev ProfiledRawJointGuardedCommonLiteralRightSeamRightOwnerControl
    (package : Package A strategy hwin initial) :=
  Σ child : TaggedChild A strategy hwin initial package,
    ProfiledRawJointGuardedCommonLiteralRightSeamTaggedRightOwner A strategy
      hwin package child

/-- All matching right-policy receiver states. -/
abbrev ProfiledRawJointGuardedCommonLiteralRightSeamRightReceiverControl
    (package : Package A strategy hwin initial) :=
  Σ child : TaggedChild A strategy hwin initial package,
    ProfiledRawJointGuardedCommonLiteralRightSeamTaggedRightReceiver A strategy
      hwin package child

/-- All left-policy owner states. -/
abbrev ProfiledRawJointGuardedCommonLiteralRightSeamLeftOwnerControl
    (package : Package A strategy hwin initial) :=
  Σ child : TaggedChild A strategy hwin initial package,
    ProfiledRawJointGuardedCommonLiteralRightSeamTaggedLeftOwner A strategy
      hwin package child

/-- All matching left-policy receiver states. -/
abbrev ProfiledRawJointGuardedCommonLiteralRightSeamLeftReceiverControl
    (package : Package A strategy hwin initial) :=
  Σ child : TaggedChild A strategy hwin initial package,
    ProfiledRawJointGuardedCommonLiteralRightSeamTaggedLeftReceiver A strategy
      hwin package child

noncomputable instance literalRightSeamRightOwnerControlFintype
    (package : Package A strategy hwin initial) :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralRightSeamRightOwnerControl A
        strategy hwin package) := by
  classical
  infer_instance

noncomputable instance literalRightSeamRightReceiverControlFintype
    (package : Package A strategy hwin initial) :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralRightSeamRightReceiverControl A
        strategy hwin package) := by
  classical
  infer_instance

noncomputable instance literalRightSeamLeftOwnerControlFintype
    (package : Package A strategy hwin initial) :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralRightSeamLeftOwnerControl A strategy
        hwin package) := by
  classical
  infer_instance

noncomputable instance literalRightSeamLeftReceiverControlFintype
    (package : Package A strategy hwin initial) :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralRightSeamLeftReceiverControl A
        strategy hwin package) := by
  classical
  infer_instance

/-! ## The checked seam installs one exact matched-right root -/

noncomputable instance literalRightSeamTaggedChildCodeDecidableEq
    (package : Package A strategy hwin initial) :
    DecidableEq (TaggedChild A strategy hwin initial package) :=
  Classical.decEq _

/-- Process one's recurrent right owner installed by the exact root-pinned
first block.  Its source is the literal macro computed from the full seam
tag, not a representative selected from the incidence code. -/
noncomputable def literalRightSeamTaggedTargetInitialRightOwner
    (package : Package A strategy hwin initial)
    (key : ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂) :
    ProfiledRawJointGuardedCommonLiteralRightSeamTaggedRightOwner A strategy
      hwin package
        (package.literalRightSeamTaggedTarget A strategy hwin key row past
          input) := by
  let child := package.literalRightSeamTaggedTarget A strategy hwin key row
    past input
  let source := package.literalRightSeamTaggedChildSource A strategy hwin child
  let policy := package.literalRightSeamTaggedChildPolicy A strategy hwin child
  let bank := package.literalRightSeamTaggedChildControllerBank A strategy hwin
    child
  let target := package.literalRightSeamTaggedChildRootMacro A strategy hwin key
    row past input
  exact initialProfiledRawJointUnitRightPolicyOwner A strategy source policy
    bank target

/-- Process two installs the matching receiver at the same exact child and
entry row. -/
noncomputable def literalRightSeamTaggedTargetInitialRightReceiver
    (package : Package A strategy hwin initial)
    (key : ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂) :
    ProfiledRawJointGuardedCommonLiteralRightSeamTaggedRightReceiver A strategy
      hwin package
        (package.literalRightSeamTaggedTarget A strategy hwin key row past
          input) := by
  let child := package.literalRightSeamTaggedTarget A strategy hwin key row
    past input
  let source := package.literalRightSeamTaggedChildSource A strategy hwin child
  let policy := package.literalRightSeamTaggedChildPolicy A strategy hwin child
  let target := package.literalRightSeamTaggedChildRootMacro A strategy hwin key
    row past input
  exact initialProfiledRawJointUnitRightPolicyReceiver A strategy source policy
    target row

/-- The first checked seam block therefore closes directly into the standard
leader-free carrier's matched-right shape.  The finite dependent child is
stored by both endpoints and is the sole recurrent policy index. -/
noncomputable def literalRightSeamTaggedTargetInitialMatchedRight
    (package : Package A strategy hwin initial)
    (key : ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂) :
    ProfiledRawJointLeaderFreeMatchedRight
      (TaggedChild A strategy hwin initial package)
      (ProfiledRawJointGuardedCommonLiteralRightSeamTaggedRightOwner A strategy
        hwin package)
      (ProfiledRawJointGuardedCommonLiteralRightSeamTaggedRightReceiver A
        strategy hwin package) :=
  let child := package.literalRightSeamTaggedTarget A strategy hwin key row
    past input
  ⟨child,
    package.literalRightSeamTaggedTargetInitialRightOwner A strategy hwin key
      row past input,
    package.literalRightSeamTaggedTargetInitialRightReceiver A strategy hwin
      key row past input⟩

@[simp] theorem literalRightSeamTaggedTargetInitialMatchedRight_key
    (package : Package A strategy hwin initial)
    (key : ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂) :
    (package.literalRightSeamTaggedTargetInitialMatchedRight A strategy hwin key
      row past input).1 =
      package.literalRightSeamTaggedTarget A strategy hwin key row past input :=
  rfl

@[simp] theorem literalRightSeamTaggedTargetInitialMatchedRight_common_source
    (package : Package A strategy hwin initial)
    (key : ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂) :
    let matched := package.literalRightSeamTaggedTargetInitialMatchedRight A
      strategy hwin key row past input
    matched.2.1.1 = matched.2.2.1 :=
  rfl

@[simp] theorem literalRightSeamTaggedTargetInitialMatchedRight_source
    (package : Package A strategy hwin initial)
    (key : ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂) :
    let matched := package.literalRightSeamTaggedTargetInitialMatchedRight A
      strategy hwin key row past input
    matched.2.1.1 =
      package.literalRightSeamTaggedChildRootMacro A strategy hwin key row past
        input :=
  rfl

/-! ## Reuse the complete indexed recurrent controller -/

/-- Root/exceptional adapter type above the exact seam child family.  Only
the finite front maps remain to be supplied by the surrounding guarded-common
controller; all recurrent transitions are already unconditional. -/
abbrev ProfiledRawJointGuardedCommonLiteralRightSeamExceptionalAdapter
    (package : Package A strategy hwin initial)
    (InitialOne : Type i₁) (InitialTwo : Type i₂)
    (ExceptionalOne : Type e₁) (ExceptionalTwo : Type e₂) :=
  ProfiledRawJointIndexedPolicyExceptionalAdapter A strategy
    (TaggedChild A strategy hwin initial package)
    (package.literalRightSeamTaggedChildSource A strategy hwin)
    (package.literalRightSeamTaggedChildPolicy A strategy hwin)
    (package.literalRightSeamTaggedChildControllerBank A strategy hwin)
    InitialOne InitialTwo ExceptionalOne ExceptionalTwo

/-- Complete model-facing leader-free recurrent kernel below the exact seam.
No transition receives a graph, an orientation, a strict-leader bit, or a
history. -/
noncomputable def literalRightSeamTaggedLeaderFreeKernel
    (package : Package A strategy hwin initial)
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    (adapter :
      ProfiledRawJointGuardedCommonLiteralRightSeamExceptionalAdapter A
        strategy hwin package InitialOne InitialTwo ExceptionalOne
        ExceptionalTwo) :
    ProfiledRawJointLeaderFreeKernel In₁ In₂ Out₁ Out₂ InitialOne
      InitialTwo ExceptionalOne ExceptionalTwo
      (TaggedChild A strategy hwin initial package)
      (ProfiledRawJointGuardedCommonLiteralRightSeamTaggedRightOwner A strategy
        hwin package)
      (ProfiledRawJointGuardedCommonLiteralRightSeamTaggedLeftReceiver A
        strategy hwin package)
      (ProfiledRawJointGuardedCommonLiteralRightSeamTaggedRightReceiver A
        strategy hwin package)
      (ProfiledRawJointGuardedCommonLiteralRightSeamTaggedLeftOwner A strategy
        hwin package) :=
  profiledRawJointIndexedPolicyLeaderFreeKernel A strategy
    (TaggedChild A strategy hwin initial package)
    (package.literalRightSeamTaggedChildSource A strategy hwin)
    (package.literalRightSeamTaggedChildPolicy A strategy hwin)
    (package.literalRightSeamTaggedChildControllerBank A strategy hwin)
    adapter

/-! ## Exact finite entry controls after the checked seam block -/

/-- Install the exact tagged ordinary right-policy root as process one's
owner control. -/
noncomputable def literalRightSeamTaggedInitialRightOwner
    (package : Package A strategy hwin initial)
    (key : ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂) :
    ProfiledRawJointGuardedCommonLiteralRightSeamRightOwnerControl A strategy
      hwin package :=
  let child := package.literalRightSeamTaggedTarget A strategy hwin key row
    past input
  let root := package.literalRightSeamTaggedChildRootMacro A strategy hwin key
    row past input
  ⟨child,
    initialProfiledRawJointUnitRightPolicyOwner A strategy
      (package.literalRightSeamTaggedChildSource A strategy hwin child)
      (package.literalRightSeamTaggedChildPolicy A strategy hwin child)
      (package.literalRightSeamTaggedChildControllerBank A strategy hwin child)
      root⟩

/-- Install the same exact tagged root as process two's receiver control at
the checked entry row. -/
noncomputable def literalRightSeamTaggedInitialRightReceiver
    (package : Package A strategy hwin initial)
    (key : ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂) :
    ProfiledRawJointGuardedCommonLiteralRightSeamRightReceiverControl A
      strategy hwin package :=
  let child := package.literalRightSeamTaggedTarget A strategy hwin key row
    past input
  let root := package.literalRightSeamTaggedChildRootMacro A strategy hwin key
    row past input
  ⟨child,
    initialProfiledRawJointUnitRightPolicyReceiver A strategy
      (package.literalRightSeamTaggedChildSource A strategy hwin child)
      (package.literalRightSeamTaggedChildPolicy A strategy hwin child)
      root row⟩

@[simp] theorem literalRightSeamTaggedInitialRightOwner_child
    (package : Package A strategy hwin initial)
    (key : ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂) :
    (package.literalRightSeamTaggedInitialRightOwner A strategy hwin key row
      past input).1 =
      package.literalRightSeamTaggedTarget A strategy hwin key row past input :=
  rfl

@[simp] theorem literalRightSeamTaggedInitialRightReceiver_child
    (package : Package A strategy hwin initial)
    (key : ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂) :
    (package.literalRightSeamTaggedInitialRightReceiver A strategy hwin key row
      past input).1 =
      package.literalRightSeamTaggedTarget A strategy hwin key row past input :=
  rfl

/-! ## The pinned rationalized letter carries the exact finite tag -/

/-- At the only exceptional letter consumed by the seam, the rationalized
true-member target is literally the root-pinned target stored in the finite
dependent tag.  This is the first-record pinning law; no later rationalized
record and no representative-by-code argument is used. -/
theorem literalRightSeamExactTruePlay_zero_target
    (package : Package A strategy hwin initial)
    (key : ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin
      package)
    (env : Nat → In₁ × In₂) (row : PairedEntryRow) :
    let installed := package.literalRightSeamInstalled A strategy hwin key
    (profiledRawJointLiteralRightBothExactTruePlay A strategy hwin installed
      env 0).2.1.target row =
      (package.literalRightSeamTaggedTarget A strategy hwin key row []
        (env 0)).2 := by
  dsimp only
  let installed := package.literalRightSeamInstalled A strategy hwin key
  let table :=
    profiledRawJointLiteralRightBothExactHeterogeneousLeftTable A strategy hwin
      installed
  have hrecords := table.memberController_records_allowed true (env 0) (env 1)
  have hfirst := hrecords.1
  let activation := profiledRawJointHybridExactLeftActivation A hwin installed
  change finiteCrossAnchorLiteralFirstAllowed
    (profiledRawJointGuardedFirstLeftReceiverStrategy A activation)
    (pairedLeftSenderStrategy activation.lambda) _ = true at hfirst
  simp only [finiteCrossAnchorLiteralFirstAllowed, decide_eq_true_eq] at hfirst
  have htarget := congrArg (fun record ↦ record.2.1.target row) hfirst
  simpa [literalRightSeamTaggedTarget,
    profiledRawJointLiteralRightBothExactTruePlay, table, treePlay,
    narrowedInducedTree, branchNode, BlockRecordMonitor.projectReceiverPlay,
    finiteCrossAnchorProjectReceiverRound] using htarget

/-- Consequently the two finite recurrent entry controls produced by the seam
store exactly the child observed in the checked true-member play. -/
theorem literalRightSeamTaggedInitial_children_eq_truePlay_zero
    (package : Package A strategy hwin initial)
    (key : ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin
      package)
    (env : Nat → In₁ × In₂) (row : PairedEntryRow) :
    let installed := package.literalRightSeamInstalled A strategy hwin key
    let playedChild : TaggedChild A strategy hwin initial package :=
      ⟨key,
        (profiledRawJointLiteralRightBothExactTruePlay A strategy hwin installed
          env 0).2.1.target row⟩
    (package.literalRightSeamTaggedInitialRightOwner A strategy hwin key row []
        (env 0)).1 = playedChild ∧
      (package.literalRightSeamTaggedInitialRightReceiver A strategy hwin key
        row [] (env 0)).1 = playedChild := by
  dsimp only
  have htarget := package.literalRightSeamExactTruePlay_zero_target A strategy
    hwin key env row
  have htag :
      package.literalRightSeamTaggedTarget A strategy hwin key row []
          (env 0) =
        ⟨key,
          (profiledRawJointLiteralRightBothExactTruePlay A strategy hwin
            (package.literalRightSeamInstalled A strategy hwin key) env
            0).2.1.target row⟩ := by
    apply Sigma.ext
    · rfl
    · exact heq_of_eq htarget.symm
  constructor
  · rw [literalRightSeamTaggedInitialRightOwner_child]
    exact htag
  · rw [literalRightSeamTaggedInitialRightReceiver_child]
    exact htag

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
