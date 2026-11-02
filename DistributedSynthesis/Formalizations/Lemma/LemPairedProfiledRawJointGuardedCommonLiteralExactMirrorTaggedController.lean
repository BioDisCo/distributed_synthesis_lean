/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralExactMirrorSeam
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralHeterogeneousSeamTaggedFamily
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointIndexedPolicyLeaderFreeKernel

/-!
# Finite exact tagged controller below the mirror literal seam

The process-one mirror seam closes an exact root-pinned right block into an
ordinary left-policy continuation.  A bare incidence code cannot select that
continuation: the ordinary policy depends on the literal child of one fixed
semantic occurrence.  This module therefore retains the same finite
decorated-state/input key used to select the seam table and adds the exact
dependent child emitted by that table.

The occurrence representative is deliberately reused from
`literalRightSeamPointAt`.  Thus the mirror seam and its recurrent handoff are
not allowed to choose separate same-code witnesses.  Executable controls
contain only the resulting finite tag and finite controller states; their
steps receive no graph, orientation, leader bit, history, or view.
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

/-! ## One finite key and one exact right-root child -/

/-- The mirror seam uses exactly the same decorated-state/input key and hence
the same chosen semantic occurrence as the process-two seam. -/
abbrev ProfiledRawJointGuardedCommonLiteralLeftSeamKey
    (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin package

noncomputable instance literalLeftSeamKeyFintype
    (package : Package A strategy hwin initial) :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralLeftSeamKey A strategy hwin
        package) := by
  infer_instance

/-- Policy-free installed child data selected from the representative already
fixed by the decorated package. -/
def literalLeftSeamInstalled
    (package : Package A strategy hwin initial)
    (key : ProfiledRawJointGuardedCommonLiteralLeftSeamKey A strategy hwin
      package) : ProfiledRawJointHybridCommonMoveData A strategy :=
  package.literalRightSeamInstalled A strategy hwin key

/-- Exact semantic source selected by the root-pinned right first block. -/
noncomputable abbrev ProfiledRawJointGuardedCommonLiteralLeftSeamSelectedSource
    (package : Package A strategy hwin initial)
    (key : ProfiledRawJointGuardedCommonLiteralLeftSeamKey A strategy hwin
      package) :=
  profiledRawJointRootPinnedSelectedSource A strategy
    ((package.literalLeftSeamInstalled A strategy hwin key).world
      |>.oneSidedState A .right)
    (profiledRawJointHybridExactRightRootPredicate A
      (package.literalLeftSeamInstalled A strategy hwin key))
    (profiledRawJointHybridExactRightPolicy A hwin
      (package.literalLeftSeamInstalled A strategy hwin key))

/-- Full finite tag of a literal left/`both` seam child. -/
abbrev ProfiledRawJointGuardedCommonLiteralLeftSeamTaggedChildCode
    (package : Package A strategy hwin initial) :=
  Σ key : ProfiledRawJointGuardedCommonLiteralLeftSeamKey A strategy hwin
      package,
    ProfiledRawJointOneSidedLiteralChildCode A strategy
      (ProfiledRawJointGuardedCommonLiteralLeftSeamSelectedSource A strategy
        hwin package key)

private abbrev TaggedChild (initial : CommonPoint A strategy)
    (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralLeftSeamTaggedChildCode A strategy hwin
    package

noncomputable instance literalLeftSeamTaggedChildCodeFintype
    (package : Package A strategy hwin initial) :
    Fintype (TaggedChild A strategy hwin initial package) := by
  classical
  infer_instance

noncomputable instance literalLeftSeamTaggedChildCodeDecidableEq
    (package : Package A strategy hwin initial) :
    DecidableEq (TaggedChild A strategy hwin initial package) :=
  Classical.decEq _

/-- Recover the exact literal semantic child from the full tag. -/
noncomputable def literalLeftSeamTaggedChildSource
    (package : Package A strategy hwin initial)
    (child : TaggedChild A strategy hwin initial package) :
    ProfiledRawJointOneSidedSemanticState A strategy (I := Unit) :=
  profiledRawJointOneSidedLiteralChildSource A strategy
    (ProfiledRawJointGuardedCommonLiteralLeftSeamSelectedSource A strategy hwin
      package child.1) child.2

@[simp] theorem literalLeftSeamTaggedChildSource_code
    (package : Package A strategy hwin initial)
    (child : TaggedChild A strategy hwin initial package) :
    (package.literalLeftSeamTaggedChildSource A strategy hwin child).code A =
      child.2.1 :=
  profiledRawJointOneSidedLiteralChildSource_code A strategy
    (ProfiledRawJointGuardedCommonLiteralLeftSeamSelectedSource A strategy hwin
      package child.1) child.2

/-- Recover the ordinary policy selected by this exact dependent child. -/
noncomputable def literalLeftSeamTaggedChildPolicy
    (package : Package A strategy hwin initial)
    (child : TaggedChild A strategy hwin initial package) :
    ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      ((package.literalLeftSeamTaggedChildSource A strategy hwin child).code
        A) := by
  let installed := package.literalLeftSeamInstalled A strategy hwin child.1
  let policy := profiledRawJointRootPinnedLiteralChildPolicyBank A strategy
    hwin (installed.world.oneSidedState A .right)
      (profiledRawJointHybridExactRightRootPredicate A installed)
      (profiledRawJointHybridExactRightPolicy A hwin installed) child.2
  simpa only [literalLeftSeamTaggedChildSource,
    profiledRawJointOneSidedLiteralChildSource_code] using policy

/-- Add the finite seam key to the exact target emitted by the root-pinned
right first block. -/
def literalLeftSeamTaggedTarget
    (package : Package A strategy hwin initial)
    (key : ProfiledRawJointGuardedCommonLiteralLeftSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (input : In₂ × In₁) : TaggedChild A strategy hwin initial package :=
  let installed := package.literalLeftSeamInstalled A strategy hwin key
  ⟨key,
    profiledRawJointGuardedFirstRightTarget A strategy
      (installed.world.oneSidedState A .right)
      (profiledRawJointHybridExactRightRootPredicate A installed)
      (profiledRawJointHybridExactRightPolicy A hwin installed)
      row past input⟩

/-- The exact tag recovers the ordinary left-policy root selected by the
root-pinned right block. -/
noncomputable def literalLeftSeamTaggedChildRootMacro
    (package : Package A strategy hwin initial)
    (key : ProfiledRawJointGuardedCommonLiteralLeftSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (input : In₂ × In₁) :
    let child := package.literalLeftSeamTaggedTarget A strategy hwin key row
      past input
    ProfiledRawJointUnitLeftPolicyMacro A strategy
      ((package.literalLeftSeamTaggedChildSource A strategy hwin child).code A)
      (package.literalLeftSeamTaggedChildPolicy A strategy hwin child) := by
  let installed := package.literalLeftSeamInstalled A strategy hwin key
  let literal := profiledRawJointGuardedFirstRightTarget A strategy
    (installed.world.oneSidedState A .right)
    (profiledRawJointHybridExactRightRootPredicate A installed)
    (profiledRawJointHybridExactRightPolicy A hwin installed) row past input
  let child := package.literalLeftSeamTaggedTarget A strategy hwin key row past
    input
  let policy := package.literalLeftSeamTaggedChildPolicy A strategy hwin child
  let activation := profiledRawJointHybridExactRightActivation A hwin installed
  let slot := profiledRawRightChildSlot A (installed.world.procOneSlot A)
    activation.lambda row past input
  have hliteral : literal.1.family.left () = some slot := by
    exact activation.target_active_slot row past input
  have hsource :
      (package.literalLeftSeamTaggedChildSource A strategy hwin child).code A =
        literal.1 := by
    exact package.literalLeftSeamTaggedChildSource_code A strategy hwin child
  have hrootCode :
      (policy.run []).1 =
        (package.literalLeftSeamTaggedChildSource A strategy hwin child).code A := by
    have hroot := congrArg Prod.fst policy.accepts.1.1
    simpa [sourceFreeBeliefCodeParityRunAutomaton] using hroot
  exact {
    state := policy.run []
    reachable := ⟨[], rfl⟩
    slot := slot
    active_slot := by
      rw [hrootCode, hsource]
      exact hliteral }

@[simp] theorem literalLeftSeamTaggedChildRootMacro_state
    (package : Package A strategy hwin initial)
    (key : ProfiledRawJointGuardedCommonLiteralLeftSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (input : In₂ × In₁) :
    (package.literalLeftSeamTaggedChildRootMacro A strategy hwin key row past
      input).state =
      (package.literalLeftSeamTaggedChildPolicy A strategy hwin
        (package.literalLeftSeamTaggedTarget A strategy hwin key row past
          input)).run [] :=
  rfl

@[simp] theorem literalLeftSeamTaggedChildRootMacro_slot
    (package : Package A strategy hwin initial)
    (key : ProfiledRawJointGuardedCommonLiteralLeftSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (input : In₂ × In₁) :
    (package.literalLeftSeamTaggedChildRootMacro A strategy hwin key row past
      input).slot =
      let installed := package.literalLeftSeamInstalled A strategy hwin key
      let activation := profiledRawJointHybridExactRightActivation A hwin
        installed
      profiledRawRightChildSlot A (installed.world.procOneSlot A)
        activation.lambda row past input :=
  rfl

/-! ## Exact recurrent bank and its finite dependent families -/

noncomputable def literalLeftSeamTaggedChildControllerBank
    (package : Package A strategy hwin initial)
    (child : TaggedChild A strategy hwin initial package) :
    ProfiledRawJointUnitPolicyControllerBank A strategy
      (package.literalLeftSeamTaggedChildSource A strategy hwin child)
      (package.literalLeftSeamTaggedChildPolicy A strategy hwin child) :=
  profiledRawJointUnitPolicyControllerBank A strategy
    (package.literalLeftSeamTaggedChildSource A strategy hwin child)
    (package.literalLeftSeamTaggedChildPolicy A strategy hwin child)

abbrev ProfiledRawJointGuardedCommonLiteralLeftSeamTaggedRightOwner
    (package : Package A strategy hwin initial)
    (child : TaggedChild A strategy hwin initial package) :=
  ProfiledRawJointUnitPolicyRightOwner A strategy
    (package.literalLeftSeamTaggedChildSource A strategy hwin child)
    (package.literalLeftSeamTaggedChildPolicy A strategy hwin child)
    (package.literalLeftSeamTaggedChildControllerBank A strategy hwin child) ()

abbrev ProfiledRawJointGuardedCommonLiteralLeftSeamTaggedLeftReceiver
    (package : Package A strategy hwin initial)
    (child : TaggedChild A strategy hwin initial package) :=
  ProfiledRawJointUnitPolicyLeftReceiver A strategy
    (package.literalLeftSeamTaggedChildSource A strategy hwin child)
    (package.literalLeftSeamTaggedChildPolicy A strategy hwin child) ()

abbrev ProfiledRawJointGuardedCommonLiteralLeftSeamTaggedRightReceiver
    (package : Package A strategy hwin initial)
    (child : TaggedChild A strategy hwin initial package) :=
  ProfiledRawJointUnitPolicyRightReceiver A strategy
    (package.literalLeftSeamTaggedChildSource A strategy hwin child)
    (package.literalLeftSeamTaggedChildPolicy A strategy hwin child) ()

abbrev ProfiledRawJointGuardedCommonLiteralLeftSeamTaggedLeftOwner
    (package : Package A strategy hwin initial)
    (child : TaggedChild A strategy hwin initial package) :=
  ProfiledRawJointUnitPolicyLeftOwner A strategy
    (package.literalLeftSeamTaggedChildSource A strategy hwin child)
    (package.literalLeftSeamTaggedChildPolicy A strategy hwin child)
    (package.literalLeftSeamTaggedChildControllerBank A strategy hwin child) ()

noncomputable instance literalLeftSeamTaggedRightOwnerFintype
    (package : Package A strategy hwin initial)
    (child : TaggedChild A strategy hwin initial package) :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralLeftSeamTaggedRightOwner A strategy
        hwin package child) := by
  classical
  infer_instance

noncomputable instance literalLeftSeamTaggedLeftReceiverFintype
    (package : Package A strategy hwin initial)
    (child : TaggedChild A strategy hwin initial package) :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralLeftSeamTaggedLeftReceiver A strategy
        hwin package child) := by
  classical
  infer_instance

noncomputable instance literalLeftSeamTaggedRightReceiverFintype
    (package : Package A strategy hwin initial)
    (child : TaggedChild A strategy hwin initial package) :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralLeftSeamTaggedRightReceiver A
        strategy hwin package child) := by
  classical
  infer_instance

noncomputable instance literalLeftSeamTaggedLeftOwnerFintype
    (package : Package A strategy hwin initial)
    (child : TaggedChild A strategy hwin initial package) :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralLeftSeamTaggedLeftOwner A strategy
        hwin package child) := by
  classical
  infer_instance

/-! ## Uniform finite sums for executable endpoint controls -/

abbrev ProfiledRawJointGuardedCommonLiteralLeftSeamRightOwnerControl
    (package : Package A strategy hwin initial) :=
  Σ child : TaggedChild A strategy hwin initial package,
    ProfiledRawJointGuardedCommonLiteralLeftSeamTaggedRightOwner A strategy
      hwin package child

abbrev ProfiledRawJointGuardedCommonLiteralLeftSeamLeftReceiverControl
    (package : Package A strategy hwin initial) :=
  Σ child : TaggedChild A strategy hwin initial package,
    ProfiledRawJointGuardedCommonLiteralLeftSeamTaggedLeftReceiver A strategy
      hwin package child

abbrev ProfiledRawJointGuardedCommonLiteralLeftSeamRightReceiverControl
    (package : Package A strategy hwin initial) :=
  Σ child : TaggedChild A strategy hwin initial package,
    ProfiledRawJointGuardedCommonLiteralLeftSeamTaggedRightReceiver A strategy
      hwin package child

abbrev ProfiledRawJointGuardedCommonLiteralLeftSeamLeftOwnerControl
    (package : Package A strategy hwin initial) :=
  Σ child : TaggedChild A strategy hwin initial package,
    ProfiledRawJointGuardedCommonLiteralLeftSeamTaggedLeftOwner A strategy
      hwin package child

noncomputable instance literalLeftSeamRightOwnerControlFintype
    (package : Package A strategy hwin initial) :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralLeftSeamRightOwnerControl A strategy
        hwin package) := by
  classical
  infer_instance

noncomputable instance literalLeftSeamLeftReceiverControlFintype
    (package : Package A strategy hwin initial) :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralLeftSeamLeftReceiverControl A
        strategy hwin package) := by
  classical
  infer_instance

noncomputable instance literalLeftSeamRightReceiverControlFintype
    (package : Package A strategy hwin initial) :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralLeftSeamRightReceiverControl A
        strategy hwin package) := by
  classical
  infer_instance

noncomputable instance literalLeftSeamLeftOwnerControlFintype
    (package : Package A strategy hwin initial) :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralLeftSeamLeftOwnerControl A strategy
        hwin package) := by
  classical
  infer_instance

/-! ## Exact matched-left entry and complete recurrent kernel -/

noncomputable def literalLeftSeamTaggedTargetInitialLeftReceiver
    (package : Package A strategy hwin initial)
    (key : ProfiledRawJointGuardedCommonLiteralLeftSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (input : In₂ × In₁) :
    ProfiledRawJointGuardedCommonLiteralLeftSeamTaggedLeftReceiver A strategy
      hwin package
        (package.literalLeftSeamTaggedTarget A strategy hwin key row past
          input) := by
  let child := package.literalLeftSeamTaggedTarget A strategy hwin key row past
    input
  let source := package.literalLeftSeamTaggedChildSource A strategy hwin child
  let policy := package.literalLeftSeamTaggedChildPolicy A strategy hwin child
  let target := package.literalLeftSeamTaggedChildRootMacro A strategy hwin key
    row past input
  exact initialProfiledRawJointUnitLeftPolicyReceiver A strategy source policy
    target row

noncomputable def literalLeftSeamTaggedTargetInitialLeftOwner
    (package : Package A strategy hwin initial)
    (key : ProfiledRawJointGuardedCommonLiteralLeftSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (input : In₂ × In₁) :
    ProfiledRawJointGuardedCommonLiteralLeftSeamTaggedLeftOwner A strategy hwin
      package
        (package.literalLeftSeamTaggedTarget A strategy hwin key row past
          input) := by
  let child := package.literalLeftSeamTaggedTarget A strategy hwin key row past
    input
  let source := package.literalLeftSeamTaggedChildSource A strategy hwin child
  let policy := package.literalLeftSeamTaggedChildPolicy A strategy hwin child
  let bank := package.literalLeftSeamTaggedChildControllerBank A strategy hwin
    child
  let target := package.literalLeftSeamTaggedChildRootMacro A strategy hwin key
    row past input
  exact initialProfiledRawJointUnitLeftPolicyOwner A strategy source policy bank
    target

/-- Exact integration into the standard leader-free matched-left invariant. -/
noncomputable def literalLeftSeamTaggedTargetInitialMatchedLeft
    (package : Package A strategy hwin initial)
    (key : ProfiledRawJointGuardedCommonLiteralLeftSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (input : In₂ × In₁) :
    ProfiledRawJointLeaderFreeMatchedLeft
      (TaggedChild A strategy hwin initial package)
      (ProfiledRawJointGuardedCommonLiteralLeftSeamTaggedLeftReceiver A strategy
        hwin package)
      (ProfiledRawJointGuardedCommonLiteralLeftSeamTaggedLeftOwner A strategy
        hwin package) :=
  let child := package.literalLeftSeamTaggedTarget A strategy hwin key row past
    input
  ⟨child,
    package.literalLeftSeamTaggedTargetInitialLeftReceiver A strategy hwin key
      row past input,
    package.literalLeftSeamTaggedTargetInitialLeftOwner A strategy hwin key row
      past input⟩

@[simp] theorem literalLeftSeamTaggedTargetInitialMatchedLeft_key
    (package : Package A strategy hwin initial)
    (key : ProfiledRawJointGuardedCommonLiteralLeftSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (input : In₂ × In₁) :
    (package.literalLeftSeamTaggedTargetInitialMatchedLeft A strategy hwin key
      row past input).1 =
      package.literalLeftSeamTaggedTarget A strategy hwin key row past input :=
  rfl

@[simp] theorem literalLeftSeamTaggedTargetInitialMatchedLeft_common_source
    (package : Package A strategy hwin initial)
    (key : ProfiledRawJointGuardedCommonLiteralLeftSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (input : In₂ × In₁) :
    let matched := package.literalLeftSeamTaggedTargetInitialMatchedLeft A
      strategy hwin key row past input
    matched.2.1.1 = matched.2.2.1 :=
  rfl

@[simp] theorem literalLeftSeamTaggedTargetInitialMatchedLeft_source
    (package : Package A strategy hwin initial)
    (key : ProfiledRawJointGuardedCommonLiteralLeftSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (input : In₂ × In₁) :
    let matched := package.literalLeftSeamTaggedTargetInitialMatchedLeft A
      strategy hwin key row past input
    matched.2.1.1 =
      package.literalLeftSeamTaggedChildRootMacro A strategy hwin key row past
        input :=
  rfl

abbrev ProfiledRawJointGuardedCommonLiteralLeftSeamExceptionalAdapter
    (package : Package A strategy hwin initial)
    (InitialOne : Type i₁) (InitialTwo : Type i₂)
    (ExceptionalOne : Type e₁) (ExceptionalTwo : Type e₂) :=
  ProfiledRawJointIndexedPolicyExceptionalAdapter A strategy
    (TaggedChild A strategy hwin initial package)
    (package.literalLeftSeamTaggedChildSource A strategy hwin)
    (package.literalLeftSeamTaggedChildPolicy A strategy hwin)
    (package.literalLeftSeamTaggedChildControllerBank A strategy hwin)
    InitialOne InitialTwo ExceptionalOne ExceptionalTwo

/-- Complete indexed recurrent kernel below the mirror seam. -/
noncomputable def literalLeftSeamTaggedLeaderFreeKernel
    (package : Package A strategy hwin initial)
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    (adapter :
      ProfiledRawJointGuardedCommonLiteralLeftSeamExceptionalAdapter A strategy
        hwin package InitialOne InitialTwo ExceptionalOne ExceptionalTwo) :
    ProfiledRawJointLeaderFreeKernel In₁ In₂ Out₁ Out₂ InitialOne InitialTwo
      ExceptionalOne ExceptionalTwo
      (TaggedChild A strategy hwin initial package)
      (ProfiledRawJointGuardedCommonLiteralLeftSeamTaggedRightOwner A strategy
        hwin package)
      (ProfiledRawJointGuardedCommonLiteralLeftSeamTaggedLeftReceiver A strategy
        hwin package)
      (ProfiledRawJointGuardedCommonLiteralLeftSeamTaggedRightReceiver A
        strategy hwin package)
      (ProfiledRawJointGuardedCommonLiteralLeftSeamTaggedLeftOwner A strategy
        hwin package) :=
  profiledRawJointIndexedPolicyLeaderFreeKernel A strategy
    (TaggedChild A strategy hwin initial package)
    (package.literalLeftSeamTaggedChildSource A strategy hwin)
    (package.literalLeftSeamTaggedChildPolicy A strategy hwin)
    (package.literalLeftSeamTaggedChildControllerBank A strategy hwin) adapter

/-! ## Exact finite endpoint entries -/

noncomputable def literalLeftSeamTaggedInitialLeftReceiver
    (package : Package A strategy hwin initial)
    (key : ProfiledRawJointGuardedCommonLiteralLeftSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (input : In₂ × In₁) :
    ProfiledRawJointGuardedCommonLiteralLeftSeamLeftReceiverControl A strategy
      hwin package :=
  let child := package.literalLeftSeamTaggedTarget A strategy hwin key row past
    input
  let root := package.literalLeftSeamTaggedChildRootMacro A strategy hwin key row
    past input
  ⟨child,
    initialProfiledRawJointUnitLeftPolicyReceiver A strategy
      (package.literalLeftSeamTaggedChildSource A strategy hwin child)
      (package.literalLeftSeamTaggedChildPolicy A strategy hwin child) root row⟩

noncomputable def literalLeftSeamTaggedInitialLeftOwner
    (package : Package A strategy hwin initial)
    (key : ProfiledRawJointGuardedCommonLiteralLeftSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (input : In₂ × In₁) :
    ProfiledRawJointGuardedCommonLiteralLeftSeamLeftOwnerControl A strategy hwin
      package :=
  let child := package.literalLeftSeamTaggedTarget A strategy hwin key row past
    input
  let root := package.literalLeftSeamTaggedChildRootMacro A strategy hwin key row
    past input
  ⟨child,
    initialProfiledRawJointUnitLeftPolicyOwner A strategy
      (package.literalLeftSeamTaggedChildSource A strategy hwin child)
      (package.literalLeftSeamTaggedChildPolicy A strategy hwin child)
      (package.literalLeftSeamTaggedChildControllerBank A strategy hwin child)
      root⟩

@[simp] theorem literalLeftSeamTaggedInitialLeftReceiver_child
    (package : Package A strategy hwin initial)
    (key : ProfiledRawJointGuardedCommonLiteralLeftSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (input : In₂ × In₁) :
    (package.literalLeftSeamTaggedInitialLeftReceiver A strategy hwin key row
      past input).1 =
      package.literalLeftSeamTaggedTarget A strategy hwin key row past input :=
  rfl

@[simp] theorem literalLeftSeamTaggedInitialLeftOwner_child
    (package : Package A strategy hwin initial)
    (key : ProfiledRawJointGuardedCommonLiteralLeftSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (input : In₂ × In₁) :
    (package.literalLeftSeamTaggedInitialLeftOwner A strategy hwin key row past
      input).1 =
      package.literalLeftSeamTaggedTarget A strategy hwin key row past input :=
  rfl

/-! ## The rationalized seam and the handoff carry one literal child -/

/-- First-record pinning identifies the target read from the exact true member
with the dependent target stored in the finite seam tag. -/
theorem literalLeftSeamExactTruePlay_zero_target
    (package : Package A strategy hwin initial)
    (key : ProfiledRawJointGuardedCommonLiteralLeftSeamKey A strategy hwin
      package)
    (env : Nat → In₂ × In₁) (row : PairedEntryRow) :
    let installed := package.literalLeftSeamInstalled A strategy hwin key
    (profiledRawJointLiteralLeftBothExactTruePlay A strategy hwin installed env
      0).2.1.target row =
      (package.literalLeftSeamTaggedTarget A strategy hwin key row []
        (env 0)).2 := by
  dsimp only
  let installed := package.literalLeftSeamInstalled A strategy hwin key
  let table :=
    profiledRawJointLiteralLeftBothExactHeterogeneousRightTable A strategy hwin
      installed
  have hrecords := table.memberController_records_allowed true (env 0) (env 1)
  have hfirst := hrecords.1
  let activation := profiledRawJointHybridExactRightActivation A hwin installed
  change finiteCrossAnchorLiteralFirstAllowed
    (profiledRawJointGuardedFirstRightReceiverStrategy A activation)
    (pairedRightSenderStrategy activation.lambda) _ = true at hfirst
  simp only [finiteCrossAnchorLiteralFirstAllowed, decide_eq_true_eq] at hfirst
  have htarget := congrArg (fun record ↦ record.2.1.target row) hfirst
  simpa [literalLeftSeamTaggedTarget,
    profiledRawJointLiteralLeftBothExactTruePlay, table, treePlay,
    narrowedInducedTree, branchNode, BlockRecordMonitor.projectReceiverPlay,
    finiteCrossAnchorProjectReceiverRound] using htarget

/-- Exact integration theorem: both finite matched-left endpoint entries store
the literal child actually observed in the checked true-member play. -/
theorem literalLeftSeamTaggedInitial_children_eq_truePlay_zero
    (package : Package A strategy hwin initial)
    (key : ProfiledRawJointGuardedCommonLiteralLeftSeamKey A strategy hwin
      package)
    (env : Nat → In₂ × In₁) (row : PairedEntryRow) :
    let installed := package.literalLeftSeamInstalled A strategy hwin key
    let playedChild : TaggedChild A strategy hwin initial package :=
      ⟨key,
        (profiledRawJointLiteralLeftBothExactTruePlay A strategy hwin installed
          env 0).2.1.target row⟩
    (package.literalLeftSeamTaggedInitialLeftReceiver A strategy hwin key row []
        (env 0)).1 = playedChild ∧
      (package.literalLeftSeamTaggedInitialLeftOwner A strategy hwin key row []
        (env 0)).1 = playedChild := by
  dsimp only
  have htarget := package.literalLeftSeamExactTruePlay_zero_target A strategy
    hwin key env row
  have htag :
      package.literalLeftSeamTaggedTarget A strategy hwin key row [] (env 0) =
        ⟨key,
          (profiledRawJointLiteralLeftBothExactTruePlay A strategy hwin
            (package.literalLeftSeamInstalled A strategy hwin key) env
            0).2.1.target row⟩ := by
    exact congrArg
      (fun child : ProfiledRawJointOneSidedLiteralChildCode A strategy
          (ProfiledRawJointGuardedCommonLiteralLeftSeamSelectedSource A
            strategy hwin package key) ↦
        (⟨key, child⟩ : TaggedChild A strategy hwin initial package))
      htarget.symm
  constructor
  · rw [literalLeftSeamTaggedInitialLeftReceiver_child]
    exact htag
  · rw [literalLeftSeamTaggedInitialLeftOwner_child]
    exact htag

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
