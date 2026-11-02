/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionBranchSelection

/-!
# Feasibility audit for the strict-prefix continuation bridge

The entry-selection control retains a strict seed beside a live owner backed
by the recurrent common occurrence.  This file separates the statement that
the current control actually proves from the stronger statement needed to
resume the seed's independently selected ordinary policy.

The positive result is exact: from the fresh fork, an inductive finite-prefix
relation follows the live guarded owner through every blind non-receive while
leaving the strict seed unchanged.  This is precisely the behavior of the
compiled branch transition.

That relation contains no control of the ordinary child policy stored in the
strict seed.  The policy was selected independently of the guarded common
pair, and the current interface supplies no equality between their sender
tables.  The final section gives a finite checked counterexample to the
abstract inference that root output compatibility alone forces one-step
compatibility.  Thus a strict-policy continuation bridge cannot be justified
from root compatibility and separate finite-state regularity alone.

This counterexample does not assert that no stronger theorem about the
underlying semantic trees exists.  It identifies the extra fact that must be
proved or built into the regularization: a joint sender table, or an explicit
relation between the two controller positions that is preserved by every
blind input.
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

private abbrev CommonOne (initial : CommonPoint A strategy) :=
  ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonOneState
    A strategy hwin initial

private abbrev CommonTwo (initial : CommonPoint A strategy) :=
  ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonTwoState
    A strategy hwin initial

private abbrev StrictRightSeed (initial : CommonPoint A strategy) :=
  ProfiledRawJointGuardedCommonLiteralCrossRootPinnedStrictRightSeed A
    strategy hwin initial

private abbrev StrictLeftSeed (initial : CommonPoint A strategy) :=
  ProfiledRawJointGuardedCommonLiteralCrossRootPinnedStrictLeftSeed A
    strategy hwin initial

private abbrev OneOwnerBacked (initial : CommonPoint A strategy) :=
  ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOneOwnerBacked
    A strategy hwin initial

private abbrev TwoOwnerBacked (initial : CommonPoint A strategy) :=
  ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoOwnerBacked
    A strategy hwin initial

private abbrev OneBranch (initial : CommonPoint A strategy) :=
  ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOneBranch
    A strategy hwin initial

private abbrev TwoBranch (initial : CommonPoint A strategy) :=
  ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoBranch
    A strategy hwin initial

/-! ## What the current payload really tracks -/

/-- A process-one open branch after a finite blind prefix.  The strict-left
seed is fixed once and for all.  Only the right owner backed by the dormant
common occurrence advances. -/
inductive
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOneStrictPrefix
    {initial : CommonPoint A strategy}
    (seed : StrictLeftSeed A strategy hwin initial)
    (common : CommonOne A strategy hwin initial) :
    OneOwnerBacked A strategy hwin initial → Prop
  | root :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOneStrictPrefix
        seed common
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOneBackedAtCommon
          A strategy hwin common)
  | noRecv {backed : OneOwnerBacked A strategy hwin initial}
      (hprefix :
        ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOneStrictPrefix
          seed common backed)
      (input : In₁) :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOneStrictPrefix
        seed common
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOneBackedNoRecv
          A strategy hwin backed input).1

/-- Process-two mirror. -/
inductive
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoStrictPrefix
    {initial : CommonPoint A strategy}
    (seed : StrictRightSeed A strategy hwin initial)
    (common : CommonTwo A strategy hwin initial) :
    TwoOwnerBacked A strategy hwin initial → Prop
  | root :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoStrictPrefix
        seed common
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoBackedAtCommon
          A strategy hwin common)
  | noRecv {backed : TwoOwnerBacked A strategy hwin initial}
      (hprefix :
        ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoStrictPrefix
          seed common backed)
      (input : In₂) :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoStrictPrefix
        seed common
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoBackedNoRecv
          A strategy hwin backed input).1

/-- At a fresh process-one fork, the pending payload is exactly the root of
the strict-prefix relation. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOneStrictPrefix_fresh
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) :
    let pending :=
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOnePendingAt
        A strategy hwin initial entry input member
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOneStrictPrefix
      A strategy hwin pending.1 pending.2.common pending.2 := by
  exact
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOneStrictPrefix.root

/-- Process-two fresh root. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoStrictPrefix_fresh
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) :
    let pending :=
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoPendingAt
        A strategy hwin initial entry input member
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoStrictPrefix
      A strategy hwin pending.1 pending.2.common pending.2 := by
  exact
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoStrictPrefix.root

/-- The exact one-step closure supplied by the current process-one payload. -/
theorem
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOneStrictPrefix.step
    {initial : CommonPoint A strategy}
    {seed : StrictLeftSeed A strategy hwin initial}
    {common : CommonOne A strategy hwin initial}
    {backed : OneOwnerBacked A strategy hwin initial}
    (hprefix :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOneStrictPrefix
        A strategy hwin seed common backed)
    (input : In₁) :
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOneStrictPrefix
      A strategy hwin seed common
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOneBackedNoRecv
        A strategy hwin backed input).1 :=
  .noRecv hprefix input

/-- Process-two one-step closure. -/
theorem
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoStrictPrefix.step
    {initial : CommonPoint A strategy}
    {seed : StrictRightSeed A strategy hwin initial}
    {common : CommonTwo A strategy hwin initial}
    {backed : TwoOwnerBacked A strategy hwin initial}
    (hprefix :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoStrictPrefix
        A strategy hwin seed common backed)
    (input : In₂) :
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoStrictPrefix
      A strategy hwin seed common
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoBackedNoRecv
        A strategy hwin backed input).1 :=
  .noRecv hprefix input

/-! ## The compiled strict branch uses only the guarded owner -/

/-- A process-one blind step preserves the strict seed verbatim and obtains
both its output and next control from the owner-backed transition. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOneBranchNoRecv_strict
    {initial : CommonPoint A strategy}
    (seed : StrictLeftSeed A strategy hwin initial)
    (backed : OneOwnerBacked A strategy hwin initial) (input : In₁) :
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOneBranchNoRecv
        A strategy hwin (.strictLeft seed backed) input =
      (.strictLeft seed
          (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOneBackedNoRecv
            A strategy hwin backed input).1,
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOneBackedNoRecv
          A strategy hwin backed input).2) := by
  rfl

/-- Process-two mirror. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoBranchNoRecv_strict
    {initial : CommonPoint A strategy}
    (seed : StrictRightSeed A strategy hwin initial)
    (backed : TwoOwnerBacked A strategy hwin initial) (input : In₂) :
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoBranchNoRecv
        A strategy hwin (.strictRight seed backed) input =
      (.strictRight seed
          (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoBackedNoRecv
            A strategy hwin backed input).1,
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoBackedNoRecv
          A strategy hwin backed input).2) := by
  rfl

/-- The process-one strict-prefix invariant is preserved by the actual branch
transition, but its conclusion still mentions only the guarded owner. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOneStrictPrefix_branchStep
    {initial : CommonPoint A strategy}
    {seed : StrictLeftSeed A strategy hwin initial}
    {common : CommonOne A strategy hwin initial}
    {backed : OneOwnerBacked A strategy hwin initial}
    (hprefix :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOneStrictPrefix
        A strategy hwin seed common backed)
    (input : In₁) :
    let next :=
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOneBranchNoRecv
        A strategy hwin (.strictLeft seed backed) input
    ∃ nextBacked,
      next.1 = .strictLeft seed nextBacked ∧
        ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOneStrictPrefix
          A strategy hwin seed common nextBacked := by
  refine ⟨
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionOneBackedNoRecv
      A strategy hwin backed input).1, rfl, ?_⟩
  exact hprefix.step A strategy hwin input

/-- Process-two mirror. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoStrictPrefix_branchStep
    {initial : CommonPoint A strategy}
    {seed : StrictRightSeed A strategy hwin initial}
    {common : CommonTwo A strategy hwin initial}
    {backed : TwoOwnerBacked A strategy hwin initial}
    (hprefix :
      ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoStrictPrefix
        A strategy hwin seed common backed)
    (input : In₂) :
    let next :=
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoBranchNoRecv
        A strategy hwin (.strictRight seed backed) input
    ∃ nextBacked,
      next.1 = .strictRight seed nextBacked ∧
        ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoStrictPrefix
          A strategy hwin seed common nextBacked := by
  refine ⟨
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionTwoBackedNoRecv
      A strategy hwin backed input).1, rfl, ?_⟩
  exact hprefix.step A strategy hwin input

/-! ## The strict child can be root-pinned before joint narrowing

The current seed chooses an ordinary policy from the finite child code.  For
the repaired construction, the finite entry and resolving inputs instead
determine the literal physical direction.  We may therefore take the actual
semantic child first and root-pin its move before any sender controller is
extracted.  The following definitions verify this construction separately
for the two orientations.
-/

/-- Literal strict-left child selected by the two physical entry records. -/
noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictLeftLiteralChildAt
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    ProfiledRawJointOneSidedSemanticState A strategy (I := Unit) :=
  let installed :=
    profiledRawJointGuardedCommonPointInstalled A strategy initial
  let source := installed.world.oneSidedState A .left
  source.step A
    (profiledRawJointUnitLeftActualDirection .both [entry] input)

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- The exact strict-left child has the target code emitted by the literal
second record. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictLeftLiteralChildAt_code
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    let installed :=
      profiledRawJointGuardedCommonPointInstalled A strategy initial
    let source := installed.world.oneSidedState A .left
    let predicate := profiledRawJointHybridExactLeftRootPredicate A installed
    let package := profiledRawJointHybridExactLeftPolicy A hwin installed
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictLeftLiteralChildAt
        A strategy initial entry input).code A =
      (profiledRawJointGuardedFirstLeftTarget A strategy source predicate
        package .both [entry] input).1 := by
  dsimp only
  let installed :=
    profiledRawJointGuardedCommonPointInstalled A strategy initial
  let source := installed.world.oneSidedState A .left
  let predicate := profiledRawJointHybridExactLeftRootPredicate A installed
  let package := profiledRawJointHybridExactLeftPolicy A hwin installed
  let selected := profiledRawJointRootPinnedSelectedSource A strategy source
    predicate package
  let actual := profiledRawJointUnitLeftActualDirection
    (In₁ := In₁) (In₂ := In₂) .both [entry] input
  calc
    (source.step A actual).code A =
        profiledRawJointOneSidedNext A (source.code A) (source.move A) actual :=
      ProfiledRawJointOneSidedSemanticState.step_code A source actual
    _ = profiledRawJointOneSidedNext A (selected.code A)
          (selected.move A) actual := by
      rw [profiledRawJointRootPinnedSelectedSource_code A strategy source
        predicate package,
        profiledRawJointRootPinnedSelectedSource_move A strategy source
          predicate package,
        profiledRawJointHybridExactLeft_rootMove A installed package]
    _ = (profiledRawJointGuardedFirstLeftTarget A strategy source predicate
          package .both [entry] input).1 := rfl

/-- Literal strict-right mirror. -/
noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictRightLiteralChildAt
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    ProfiledRawJointOneSidedSemanticState A strategy (I := Unit) :=
  let installed :=
    profiledRawJointGuardedCommonPointInstalled A strategy initial
  let source := installed.world.oneSidedState A .right
  source.step A
    (profiledRawJointUnitRightActualDirection .both
      [(entry.2, entry.1)] (input.2, input.1))

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- The exact strict-right child has the target code emitted by its literal
second record. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictRightLiteralChildAt_code
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    let installed :=
      profiledRawJointGuardedCommonPointInstalled A strategy initial
    let source := installed.world.oneSidedState A .right
    let predicate := profiledRawJointHybridExactRightRootPredicate A installed
    let package := profiledRawJointHybridExactRightPolicy A hwin installed
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictRightLiteralChildAt
        A strategy initial entry input).code A =
      (profiledRawJointGuardedFirstRightTarget A strategy source predicate
        package .both [(entry.2, entry.1)] (input.2, input.1)).1 := by
  dsimp only
  let installed :=
    profiledRawJointGuardedCommonPointInstalled A strategy initial
  let source := installed.world.oneSidedState A .right
  let predicate := profiledRawJointHybridExactRightRootPredicate A installed
  let package := profiledRawJointHybridExactRightPolicy A hwin installed
  let selected := profiledRawJointRootPinnedSelectedSource A strategy source
    predicate package
  let actual := profiledRawJointUnitRightActualDirection
    (In₁ := In₁) (In₂ := In₂) .both
      [(entry.2, entry.1)] (input.2, input.1)
  calc
    (source.step A actual).code A =
        profiledRawJointOneSidedNext A (source.code A) (source.move A) actual :=
      ProfiledRawJointOneSidedSemanticState.step_code A source actual
    _ = profiledRawJointOneSidedNext A (selected.code A)
          (selected.move A) actual := by
      rw [profiledRawJointRootPinnedSelectedSource_code A strategy source
        predicate package,
        profiledRawJointRootPinnedSelectedSource_move A strategy source
          predicate package,
        profiledRawJointHybridExactRight_rootMove A installed package]
    _ = (profiledRawJointGuardedFirstRightTarget A strategy source predicate
          package .both [(entry.2, entry.1)] (input.2, input.1)).1 := rfl

/-- A one-shot policy whose root move is forced to be the literal strict-left
child move.  This is construction data indexed by finite inputs, not a local
runtime observation. -/
noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictLeftChildPolicyAt
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
  let child :=
    profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictLeftLiteralChildAt
      A strategy initial entry input
  ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy child
    (fun move ↦ move = child.move A) := by
  let child :=
    profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictLeftLiteralChildAt
      A strategy initial entry input
  exact Classical.choice
    (nonempty_profiledRawJointOneSidedExactRootProvenancePolicy A strategy
      hwin child)

omit [DecidableEq In₁] [DecidableEq In₂] in
omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The chosen strict-left policy really installs the literal child move at
its root. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictLeftChildPolicyAt_rootMove
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
  let child :=
    profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictLeftLiteralChildAt
      A strategy initial entry input
  (profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictLeftChildPolicyAt
    A strategy hwin initial entry input).rootMove = child.move A := by
  dsimp only
  exact
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictLeftChildPolicyAt
      A strategy hwin initial entry input).rootMove_realizes.2.1

/-- Root-pinned strict-right mirror. -/
noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictRightChildPolicyAt
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
  let child :=
    profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictRightLiteralChildAt
      A strategy initial entry input
  ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy child
    (fun move ↦ move = child.move A) := by
  let child :=
    profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictRightLiteralChildAt
      A strategy initial entry input
  exact Classical.choice
    (nonempty_profiledRawJointOneSidedExactRootProvenancePolicy A strategy
      hwin child)

omit [DecidableEq In₁] [DecidableEq In₂] in
omit [Inhabited Out₁] [Inhabited Out₂] in
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictRightChildPolicyAt_rootMove
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
  let child :=
    profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictRightLiteralChildAt
      A strategy initial entry input
  (profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictRightChildPolicyAt
    A strategy hwin initial entry input).rootMove = child.move A := by
  dsimp only
  exact
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictRightChildPolicyAt
      A strategy hwin initial entry input).rootMove_realizes.2.1

end

end DetParityAutomaton

/-! ## Finite counterexample to a root-only bridge -/

namespace StrictPrefixBridgeDiagnostic

universe input controlOne controlTwo output

/-- Pointwise compatibility of the next sender output of two local Mealy
steps. -/
def OutputCompatible
    {Input : Type input} {ControlOne : Type controlOne}
    {ControlTwo : Type controlTwo} {Output : Type output}
    (stepOne : ControlOne → Input → ControlOne × Output)
    (stepTwo : ControlTwo → Input → ControlTwo × Output)
    (one : ControlOne) (two : ControlTwo) : Prop :=
  ∀ input, (stepOne one input).2 = (stepTwo two input).2

/-- Compatibility after both controls consume the same next input. -/
def OneStepCompatible
    {Input : Type input} {ControlOne : Type controlOne}
    {ControlTwo : Type controlTwo} {Output : Type output}
    (stepOne : ControlOne → Input → ControlOne × Output)
    (stepTwo : ControlTwo → Input → ControlTwo × Output)
    (one : ControlOne) (two : ControlTwo) : Prop :=
  ∀ input,
    OutputCompatible stepOne stepTwo
      (stepOne one input).1 (stepTwo two input).1

/-- A two-state guarded owner: the first input toggles its control, and its
output is its current control. -/
def guardedStep (control : Bool) (_input : PUnit) : Bool × Bool :=
  (!control, control)

/-- An independently selected one-state strict behavior represented on the
same two-state alphabet. -/
def strictStep (control : Bool) (_input : PUnit) : Bool × Bool :=
  (control, false)

/-- The two roots have identical outputs. -/
theorem guarded_strict_root_outputCompatible :
    OutputCompatible guardedStep strictStep false false := by
  intro input
  cases input
  rfl

/-- Nevertheless, after one common input their next outputs differ. -/
theorem guarded_strict_root_not_oneStepCompatible :
    ¬ OneStepCompatible guardedStep strictStep false false := by
  simp [OneStepCompatible, OutputCompatible, guardedStep, strictStep]

/-- Finiteness also does not make a controller state output-compatible with
its own one-step successor.  For the guarded controller the successor of
`false` is `true`, and their very next outputs already differ. -/
theorem guarded_not_outputCompatible_with_successor :
    ¬ OutputCompatible guardedStep guardedStep false
      (guardedStep false PUnit.unit).1 := by
  simp [OutputCompatible, guardedStep]

/-- Hence no theorem can infer one-step compatibility merely from finite
state and root-output compatibility.  A preserved joint-control invariant is
an additional mathematical hypothesis, not bookkeeping. -/
theorem root_compatibility_does_not_imply_one_step :
    ¬ (∀
      (stepOne stepTwo : Bool → PUnit → Bool × Bool)
      (one two : Bool),
      OutputCompatible stepOne stepTwo one two →
        OneStepCompatible stepOne stepTwo one two) := by
  intro h
  exact guarded_strict_root_not_oneStepCompatible
    (h guardedStep strictStep false false
      guarded_strict_root_outputCompatible)

end StrictPrefixBridgeDiagnostic

/-! ## The constructive repair already available in the library

The counterexample rules out a bridge between two controllers selected
independently.  It does not apply when the two obligations are rationalized
simultaneously.  A `FiniteCrossAnchorPairTable` has one sender control and
only projects the proof-side receiver component according to the hidden
anchor.  Consequently its two projections have identical sender outputs and
identical successor controls at every position, not merely at the root.
-/

namespace JointRegularizationRepair

universe a b c d e

variable {RIn : Type a} {SIn : Type b} {ROut : Type c} {SOut : Type d}
variable [Inhabited RIn] [Inhabited SIn] [Inhabited ROut]
variable [Fintype RIn] [Fintype SIn] [Fintype ROut] [Fintype SOut]
variable [DecidableEq RIn] [DecidableEq SIn]

/-- The sender-side Mealy transition exposed by one projection of a joint
cross-anchor table. -/
noncomputable def crossAnchorSenderStep
    {base : Bool → BlockRecordMonitor.{a, b, c, d, e}
      RIn SIn ROut SOut}
    {start : ∀ anchor, (base anchor).State}
    (table : FiniteCrossAnchorPairTable base start) (anchor : Bool)
    (control : (table.memberController anchor).Control) (input : SIn) :
    (table.memberController anchor).Control × SOut :=
  ((table.memberController anchor).step control input,
    ((table.memberController anchor).labelOf control).1 input)

omit [Inhabited RIn] [Inhabited SIn] [Inhabited ROut] in
/-- Joint regularization supplies the missing output compatibility at every
shared control. -/
theorem crossAnchorSenderStep_outputCompatible
    {base : Bool → BlockRecordMonitor.{a, b, c, d, e}
      RIn SIn ROut SOut}
    {start : ∀ anchor, (base anchor).State}
    (table : FiniteCrossAnchorPairTable base start)
    (left right : Bool)
    (control : (table.memberController left).Control) :
    StrictPrefixBridgeDiagnostic.OutputCompatible
      (crossAnchorSenderStep table left)
      (crossAnchorSenderStep table right) control control := by
  intro input
  exact congrFun
    (table.memberController_senderLabel_eq left right control) input

omit [Inhabited RIn] [Inhabited SIn] [Inhabited ROut] in
/-- More importantly, the shared-control relation is closed by one blind
input.  This is exactly the implication that failed for independently
selected finite controllers. -/
theorem crossAnchorSenderStep_oneStepCompatible
    {base : Bool → BlockRecordMonitor.{a, b, c, d, e}
      RIn SIn ROut SOut}
    {start : ∀ anchor, (base anchor).State}
    (table : FiniteCrossAnchorPairTable base start)
    (left right : Bool)
    (control : (table.memberController left).Control) :
    StrictPrefixBridgeDiagnostic.OneStepCompatible
      (crossAnchorSenderStep table left)
      (crossAnchorSenderStep table right) control control := by
  intro input
  have hstep := table.memberController_step_eq left right control input
  simpa [crossAnchorSenderStep, hstep] using
    crossAnchorSenderStep_outputCompatible table left right
      ((table.memberController left).step control input)

omit [Inhabited RIn] [Inhabited SIn] [Inhabited ROut] in
/-- The same joint table therefore keeps the two projected sender outputs
equal after every finite blind word. -/
theorem crossAnchorSender_afterWord_eq
    {base : Bool → BlockRecordMonitor.{a, b, c, d, e}
      RIn SIn ROut SOut}
    {start : ∀ anchor, (base anchor).State}
    (table : FiniteCrossAnchorPairTable base start)
    (left right : Bool) (word : List SIn) :
    ((table.memberController left).labeledTree word).1 =
      ((table.memberController right).labeledTree word).1 := by
  exact table.memberController_sender_eq left right word

end JointRegularizationRepair

end DistributedSynthesis
