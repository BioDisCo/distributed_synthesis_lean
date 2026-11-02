/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteCrossAnchorHeterogeneousPreselection
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionPostResolvePendingOverlap
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointSemanticSiblingFamilyNarrowing
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointFinitePhysicalSiblingFreshPolicyHandoff
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointGuardedFirstLeftBlockMonitor
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointGuardedFirstRightBlockMonitor

/-!
# Joint strict/common tables after the resolving record

At the resolving record, a one-sided block creates a fresh paired entry.  Its
one-sided actual child is the strict continuation, while the corresponding
two-sided semantic child is the common continuation.  Both children retain
the same live paired member, but they have different finite target
certificates:

* the strict receiver returns an exact literal-child subtype for the
  root-pinned one-sided policy;
* the common receiver returns an incidence code allowed by the simultaneous
  semantic sibling.

This file narrows those two obligations in one heterogeneous table.  The
table is indexed by the fresh pair's actual one-sided and `both` histories.
Thus sender sharing follows from the post-resolve pending overlap and never
uses the independently advanced all-`both` backbone.
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

/-! ## Process one: strict-left versus simultaneous -/

private noncomputable abbrev StrictLeftChild
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :=
  profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictLeftLiteralChildAt
    A strategy initial entry input

private noncomputable abbrev StrictLeftPair
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :=
  profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictLeftPairAt
    A strategy initial entry input

private noncomputable abbrev StrictLeftPolicy
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :=
  profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictLeftChildPolicyAt
    A strategy hwin initial entry input

private abbrev StrictLeftPredicate
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :=
  fun move : ProfiledRawJointLambdaFamilyMove A (I := Unit) ↦
    move = (StrictLeftChild A strategy initial entry input).move A

private noncomputable abbrev StrictLeftSource
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :=
  profiledRawRightSlotOfSemanticPair A
    (StrictLeftPair A strategy initial entry input)

private noncomputable def strictLeftParent
    (initial : CommonPoint A strategy) :
    ProfiledRawJointOneSidedSemanticState A strategy (I := Unit) :=
  (profiledRawJointGuardedCommonPointInstalled A strategy initial).world
    |>.oneSidedState A .left

private def strictLeftActual
    (entry input : In₁ × In₂) :
    ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂) :=
  profiledRawJointUnitLeftActualDirection .both [entry] input

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- The full simultaneous semantic child and the strict one-sided child have
the same live process-one pair. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictLeftSemanticChild_live
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    ((strictLeftParent A strategy initial).family.semanticChild A
        (strictLeftActual entry input).direction).right () =
      some (StrictLeftPair A strategy initial entry input) := by
  rw [ProfiledRawJointSemanticFamily.semanticChild_right_eq_leftActual]
  simpa [StrictLeftChild, strictLeftParent, strictLeftActual,
    ProfiledRawJointOneSidedSemanticState.step] using
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictLeftLiteralChildAt_live
      A strategy initial entry input)

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- The exact finite source slot of the live pair occurs in the strict
child's root code. -/
private theorem strictLeftSource_live
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    ((StrictLeftChild A strategy initial entry input).code A).family.right () =
      some (StrictLeftSource A strategy initial entry input) := by
  change
    ((StrictLeftChild A strategy initial entry input).family.code A).right () =
      some (StrictLeftSource A strategy initial entry input)
  exact congrArg
    (Option.map fun member ↦
      ((member.1.code, member.2),
        rightInitialFirstProfile member.1.lambdaOfStrategy))
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictLeftLiteralChildAt_live
      A strategy initial entry input)

/-- Exact root-pinned strict activation at the post-resolve child. -/
private noncomputable def strictLeftActivation
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    ProfiledRawJointGuardedFirstRightBlockActivation A strategy
      (StrictLeftChild A strategy initial entry input)
      (StrictLeftPredicate A strategy initial entry input)
      (StrictLeftPolicy A strategy hwin initial entry input)
      (StrictLeftSource A strategy initial entry input) :=
  Classical.choice
    (nonempty_profiledRawJointGuardedFirstRightBlockActivation A strategy
      (StrictLeftChild A strategy initial entry input)
      (StrictLeftPredicate A strategy initial entry input)
      (StrictLeftPolicy A strategy hwin initial entry input)
      (StrictLeftSource A strategy initial entry input)
      (strictLeftSource_live A strategy initial entry input))

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- The strict activation uses exactly the paired lambda materialized by the
resolving record. -/
private theorem strictLeftActivation_lambda
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    (strictLeftActivation A strategy hwin initial entry input).lambda =
      (StrictLeftPair A strategy initial entry input).1.lambdaOfStrategy := by
  apply Option.some.inj
  exact
    (strictLeftActivation A strategy hwin initial entry input).lambda_selected.symm.trans
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictLeftChildPolicyAt_rightLambda
        A strategy hwin initial entry input)

private abbrev StrictLeftReceiverOutput
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :=
  ProfiledRawJointGuardedFirstRightReceiverOutput A strategy
    (StrictLeftChild A strategy initial entry input)
    (StrictLeftPredicate A strategy initial entry input)
    (StrictLeftPolicy A strategy hwin initial entry input)

private noncomputable instance strictLeftReceiverOutputInhabited
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    Inhabited
      (StrictLeftReceiverOutput A strategy hwin initial entry input) :=
  ⟨{
    physical := default
    target := fun row ↦
      profiledRawJointGuardedFirstRightTarget A strategy
        (StrictLeftChild A strategy initial entry input)
        (StrictLeftPredicate A strategy initial entry input)
        (StrictLeftPolicy A strategy hwin initial entry input)
        row [] default }⟩

private abbrev StrictLeftMonitor
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :=
  profiledRawJointGuardedFirstRightBlockMonitor A strategy
    (StrictLeftChild A strategy initial entry input)
    (StrictLeftPredicate A strategy initial entry input)
    (StrictLeftPolicy A strategy hwin initial entry input)
    (StrictLeftSource A strategy initial entry input)

private abbrev CommonAfterLeftMonitor
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :=
  profiledRawJointRightSiblingBlockMonitor A
    (strictLeftParent A strategy initial).family
    (strictLeftActual entry input).direction
    (StrictLeftPair A strategy initial entry input) false

private def strictLeftReceiver
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    ReceiverBlockStrategy In₂ In₁
      (StrictLeftReceiverOutput A strategy hwin initial entry input) :=
  profiledRawJointGuardedFirstRightReceiverStrategy A
    (strictLeftActivation A strategy hwin initial entry input)

private def commonAfterLeftReceiver
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :=
  profiledRawJointRightSiblingReceiver A hwin
    (strictLeftParent A strategy initial).family
    (strictLeftActual entry input).direction
    (StrictLeftPair A strategy initial entry input)
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictLeftSemanticChild_live
      A strategy initial entry input) false

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The root-pinned strict receiver realizes its restarted monitor with the
sender at the pair's literal strict-left history. -/
private theorem strictLeftMonitor_realizable
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    ∀ env,
      ((StrictLeftMonitor A strategy hwin initial entry input).restartAt
        (StrictLeftMonitor A strategy hwin initial entry input).initial).WinsPlay
        (pairPlay (strictLeftReceiver A strategy hwin initial entry input)
          (blockSenderOne strategy
            (StrictLeftPair A strategy initial entry input).1.leftHistory) env) := by
  intro env
  have hreal :=
    profiledRawJointGuardedFirstRightBlockMonitor_realizable A
      (StrictLeftSource A strategy initial entry input)
      (strictLeftActivation A strategy hwin initial entry input) env
  have hsender :
      pairedRightSenderStrategy
          (strictLeftActivation A strategy hwin initial entry input).lambda =
        blockSenderOne strategy
          (StrictLeftPair A strategy initial entry input).1.leftHistory := by
    rw [strictLeftActivation_lambda A strategy hwin initial entry input]
    rfl
  rw [← hsender]
  simpa [StrictLeftMonitor, strictLeftReceiver,
    BlockRecordMonitor.restartAt] using hreal

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The simultaneous semantic sibling realizes its monitor with the sender
at the same fresh pair's literal `both` history. -/
private theorem commonAfterLeftMonitor_realizable
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    ∀ env,
      ((CommonAfterLeftMonitor A strategy initial entry input).restartAt
        (CommonAfterLeftMonitor A strategy initial entry input).initial).WinsPlay
        (pairPlay (commonAfterLeftReceiver A strategy hwin initial entry input)
          (blockSenderOne strategy
            (StrictLeftPair A strategy initial entry input).1.bothHistory) env) := by
  intro env
  have hreal := profiledRawJointRightSiblingBlockMonitor_realizable A hwin
    (strictLeftParent A strategy initial).family
    (strictLeftActual entry input).direction
    (StrictLeftPair A strategy initial entry input)
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictLeftSemanticChild_live
      A strategy initial entry input) false env
  have hsender :
      profiledRawJointRightSiblingSender A
          (StrictLeftPair A strategy initial entry input) =
        blockSenderOne strategy
          (StrictLeftPair A strategy initial entry input).1.bothHistory := by
    exact (StrictLeftPair A strategy initial entry input).1.lambdaOfStrategy_blind_eq_both
  rw [← hsender]
  simpa [CommonAfterLeftMonitor, commonAfterLeftReceiver,
    BlockRecordMonitor.restartAt] using hreal

/-- Type of the process-one post-resolve strict/common table.  The `false`
member is the exact strict continuation and the `true` member is the
simultaneous semantic sibling. -/
noncomputable abbrev
    ProfiledRawJointGuardedCommonLiteralStrictLeftPostResolveJointTableType
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :=
  FiniteCrossAnchorPairTable
    (finiteCrossAnchorHeterogeneousMonitor
      (StrictLeftMonitor A strategy hwin initial entry input)
      (CommonAfterLeftMonitor A strategy initial entry input))
    (finiteCrossAnchorHeterogeneousStart
      (StrictLeftMonitor A strategy hwin initial entry input)
      (CommonAfterLeftMonitor A strategy initial entry input)
      (StrictLeftMonitor A strategy hwin initial entry input).initial
      (CommonAfterLeftMonitor A strategy initial entry input).initial)

/-- Unconditional joint narrowing of the post-resolve strict-left and common
right-block obligations. -/
noncomputable def
    profiledRawJointGuardedCommonLiteralStrictLeftPostResolveJointTable
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    ProfiledRawJointGuardedCommonLiteralStrictLeftPostResolveJointTableType
      A strategy hwin initial entry input := by
  let pair := StrictLeftPair A strategy initial entry input
  exact finiteCrossAnchorHeterogeneousPairTableOneOfPendingOverlap strategy
    pair.1.leftHistory pair.1.bothHistory pair.1.pending
    (StrictLeftMonitor A strategy hwin initial entry input)
    (CommonAfterLeftMonitor A strategy initial entry input)
    (StrictLeftMonitor A strategy hwin initial entry input).initial
    (CommonAfterLeftMonitor A strategy initial entry input).initial
    (strictLeftReceiver A strategy hwin initial entry input)
    (commonAfterLeftReceiver A strategy hwin initial entry input)
    (strictLeftMonitor_realizable A strategy hwin initial entry input)
    (commonAfterLeftMonitor_realizable A strategy hwin initial entry input)

/-! ## Process two: strict-right versus simultaneous -/

private noncomputable abbrev StrictRightChild
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :=
  profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictRightLiteralChildAt
    A strategy initial entry input

private noncomputable abbrev StrictRightPair
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :=
  profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictRightPairAt
    A strategy initial entry input

private noncomputable abbrev StrictRightPolicy
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :=
  profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictRightChildPolicyAt
    A strategy hwin initial entry input

private abbrev StrictRightPredicate
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :=
  fun move : ProfiledRawJointLambdaFamilyMove A (I := Unit) ↦
    move = (StrictRightChild A strategy initial entry input).move A

private noncomputable abbrev StrictRightSource
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :=
  profiledRawLeftSlotOfSemanticPair A
    (StrictRightPair A strategy initial entry input)

private noncomputable def strictRightParent
    (initial : CommonPoint A strategy) :
    ProfiledRawJointOneSidedSemanticState A strategy (I := Unit) :=
  (profiledRawJointGuardedCommonPointInstalled A strategy initial).world
    |>.oneSidedState A .right

private def strictRightActual
    (entry input : In₁ × In₂) :
    ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂) :=
  profiledRawJointUnitRightActualDirection .both
    [(entry.2, entry.1)] (input.2, input.1)

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Mirror live-member equation for the full simultaneous child. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictRightSemanticChild_live
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    ((strictRightParent A strategy initial).family.semanticChild A
        (strictRightActual entry input).direction).left () =
      some (StrictRightPair A strategy initial entry input) := by
  rw [ProfiledRawJointSemanticFamily.semanticChild_left_eq_rightActual]
  simpa [StrictRightChild, strictRightParent, strictRightActual,
    ProfiledRawJointOneSidedSemanticState.step] using
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictRightLiteralChildAt_live
      A strategy initial entry input)

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
private theorem strictRightSource_live
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    ((StrictRightChild A strategy initial entry input).code A).family.left () =
      some (StrictRightSource A strategy initial entry input) := by
  change
    ((StrictRightChild A strategy initial entry input).family.code A).left () =
      some (StrictRightSource A strategy initial entry input)
  exact congrArg
    (Option.map fun member ↦
      ((member.1.code, member.2),
        leftInitialFirstProfile member.1.lambdaOfStrategy))
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictRightLiteralChildAt_live
      A strategy initial entry input)

private noncomputable def strictRightActivation
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    ProfiledRawJointGuardedFirstLeftBlockActivation A strategy
      (StrictRightChild A strategy initial entry input)
      (StrictRightPredicate A strategy initial entry input)
      (StrictRightPolicy A strategy hwin initial entry input)
      (StrictRightSource A strategy initial entry input) :=
  Classical.choice
    (nonempty_profiledRawJointGuardedFirstLeftBlockActivation A strategy
      (StrictRightChild A strategy initial entry input)
      (StrictRightPredicate A strategy initial entry input)
      (StrictRightPolicy A strategy hwin initial entry input)
      (StrictRightSource A strategy initial entry input)
      (strictRightSource_live A strategy initial entry input))

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
private theorem strictRightActivation_lambda
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    (strictRightActivation A strategy hwin initial entry input).lambda =
      (StrictRightPair A strategy initial entry input).1.lambdaOfStrategy := by
  apply Option.some.inj
  exact
    (strictRightActivation A strategy hwin initial entry input).lambda_selected.symm.trans
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictRightChildPolicyAt_leftLambda
        A strategy hwin initial entry input)

private abbrev StrictRightReceiverOutput
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :=
  ProfiledRawJointGuardedFirstLeftReceiverOutput A strategy
    (StrictRightChild A strategy initial entry input)
    (StrictRightPredicate A strategy initial entry input)
    (StrictRightPolicy A strategy hwin initial entry input)

private noncomputable instance strictRightReceiverOutputInhabited
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    Inhabited
      (StrictRightReceiverOutput A strategy hwin initial entry input) :=
  ⟨{
    physical := default
    target := fun row ↦
      profiledRawJointGuardedFirstLeftTarget A strategy
        (StrictRightChild A strategy initial entry input)
        (StrictRightPredicate A strategy initial entry input)
        (StrictRightPolicy A strategy hwin initial entry input)
        row [] default }⟩

private abbrev StrictRightMonitor
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :=
  profiledRawJointGuardedFirstLeftBlockMonitor A strategy
    (StrictRightChild A strategy initial entry input)
    (StrictRightPredicate A strategy initial entry input)
    (StrictRightPolicy A strategy hwin initial entry input)
    (StrictRightSource A strategy initial entry input)

private abbrev CommonAfterRightMonitor
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :=
  profiledRawJointLeftSiblingBlockMonitor A
    (strictRightParent A strategy initial).family
    (strictRightActual entry input).direction
    (StrictRightPair A strategy initial entry input) false

private def strictRightReceiver
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    ReceiverBlockStrategy In₁ In₂
      (StrictRightReceiverOutput A strategy hwin initial entry input) :=
  profiledRawJointGuardedFirstLeftReceiverStrategy A
    (strictRightActivation A strategy hwin initial entry input)

private def commonAfterRightReceiver
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :=
  profiledRawJointLeftSiblingReceiver A hwin
    (strictRightParent A strategy initial).family
    (strictRightActual entry input).direction
    (StrictRightPair A strategy initial entry input)
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictRightSemanticChild_live
      A strategy initial entry input) false

omit [Inhabited Out₁] [Inhabited Out₂] in
private theorem strictRightMonitor_realizable
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    ∀ env,
      ((StrictRightMonitor A strategy hwin initial entry input).restartAt
        (StrictRightMonitor A strategy hwin initial entry input).initial).WinsPlay
        (pairPlay (strictRightReceiver A strategy hwin initial entry input)
          (blockSenderTwo strategy
            (StrictRightPair A strategy initial entry input).1.rightHistory) env) := by
  intro env
  have hreal :=
    profiledRawJointGuardedFirstLeftBlockMonitor_realizable A
      (StrictRightSource A strategy initial entry input)
      (strictRightActivation A strategy hwin initial entry input) env
  have hsender :
      pairedLeftSenderStrategy
          (strictRightActivation A strategy hwin initial entry input).lambda =
        blockSenderTwo strategy
          (StrictRightPair A strategy initial entry input).1.rightHistory := by
    rw [strictRightActivation_lambda A strategy hwin initial entry input]
    rfl
  rw [← hsender]
  simpa [StrictRightMonitor, strictRightReceiver,
    BlockRecordMonitor.restartAt] using hreal

omit [Inhabited Out₁] [Inhabited Out₂] in
private theorem commonAfterRightMonitor_realizable
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    ∀ env,
      ((CommonAfterRightMonitor A strategy initial entry input).restartAt
        (CommonAfterRightMonitor A strategy initial entry input).initial).WinsPlay
        (pairPlay (commonAfterRightReceiver A strategy hwin initial entry input)
          (blockSenderTwo strategy
            (StrictRightPair A strategy initial entry input).1.bothHistory) env) := by
  intro env
  have hreal := profiledRawJointLeftSiblingBlockMonitor_realizable A hwin
    (strictRightParent A strategy initial).family
    (strictRightActual entry input).direction
    (StrictRightPair A strategy initial entry input)
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictRightSemanticChild_live
      A strategy initial entry input) false env
  have hsender :
      profiledRawJointLeftSiblingSender A
          (StrictRightPair A strategy initial entry input) =
        blockSenderTwo strategy
          (StrictRightPair A strategy initial entry input).1.bothHistory := by
    exact (StrictRightPair A strategy initial entry input).1.lambdaOfStrategy_blind_eq_both
  rw [← hsender]
  simpa [CommonAfterRightMonitor, commonAfterRightReceiver,
    BlockRecordMonitor.restartAt] using hreal

/-- Type of the process-two mirror table. -/
noncomputable abbrev
    ProfiledRawJointGuardedCommonLiteralStrictRightPostResolveJointTableType
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :=
  FiniteCrossAnchorPairTable
    (finiteCrossAnchorHeterogeneousMonitor
      (StrictRightMonitor A strategy hwin initial entry input)
      (CommonAfterRightMonitor A strategy initial entry input))
    (finiteCrossAnchorHeterogeneousStart
      (StrictRightMonitor A strategy hwin initial entry input)
      (CommonAfterRightMonitor A strategy initial entry input)
      (StrictRightMonitor A strategy hwin initial entry input).initial
      (CommonAfterRightMonitor A strategy initial entry input).initial)

/-- Unconditional joint narrowing of the post-resolve strict-right and common
left-block obligations. -/
noncomputable def
    profiledRawJointGuardedCommonLiteralStrictRightPostResolveJointTable
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    ProfiledRawJointGuardedCommonLiteralStrictRightPostResolveJointTableType
      A strategy hwin initial entry input := by
  let pair := StrictRightPair A strategy initial entry input
  exact finiteCrossAnchorHeterogeneousPairTableTwoOfPendingOverlap strategy
    pair.1.rightHistory pair.1.bothHistory pair.1.pending
    (StrictRightMonitor A strategy hwin initial entry input)
    (CommonAfterRightMonitor A strategy initial entry input)
    (StrictRightMonitor A strategy hwin initial entry input).initial
    (CommonAfterRightMonitor A strategy initial entry input).initial
    (strictRightReceiver A strategy hwin initial entry input)
    (commonAfterRightReceiver A strategy hwin initial entry input)
    (strictRightMonitor_realizable A strategy hwin initial entry input)
    (commonAfterRightMonitor_realizable A strategy hwin initial entry input)

/-! ## Shared blind-control laws -/

/-- The process-one strict and common projections have the same blind output
after every finite private-input word. -/
theorem
    profiledRawJointGuardedCommonLiteralStrictLeftPostResolveJointTable_sender_eq
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (word : List In₁) :
    let table :=
      profiledRawJointGuardedCommonLiteralStrictLeftPostResolveJointTable
        A strategy hwin initial entry input
    ((table.memberController false).labeledTree word).1 =
      ((table.memberController true).labeledTree word).1 := by
  dsimp only
  exact
    (profiledRawJointGuardedCommonLiteralStrictLeftPostResolveJointTable
      A strategy hwin initial entry input).memberController_sender_eq
        false true word

/-- At an arbitrary shared process-one control, the next control remains
independent of the strict/common interpretation. -/
theorem
    profiledRawJointGuardedCommonLiteralStrictLeftPostResolveJointTable_step_eq
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (control :
      ((profiledRawJointGuardedCommonLiteralStrictLeftPostResolveJointTable
        A strategy hwin initial entry input).memberController false).Control)
    (own : In₁) :
    let table :=
      profiledRawJointGuardedCommonLiteralStrictLeftPostResolveJointTable
        A strategy hwin initial entry input
    (table.memberController false).step control own =
      (table.memberController true).step control own := by
  dsimp only
  exact
    (profiledRawJointGuardedCommonLiteralStrictLeftPostResolveJointTable
      A strategy hwin initial entry input).memberController_step_eq
        false true control own

/-- Process-two arbitrary-prefix sender equality. -/
theorem
    profiledRawJointGuardedCommonLiteralStrictRightPostResolveJointTable_sender_eq
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (word : List In₂) :
    let table :=
      profiledRawJointGuardedCommonLiteralStrictRightPostResolveJointTable
        A strategy hwin initial entry input
    ((table.memberController false).labeledTree word).1 =
      ((table.memberController true).labeledTree word).1 := by
  dsimp only
  exact
    (profiledRawJointGuardedCommonLiteralStrictRightPostResolveJointTable
      A strategy hwin initial entry input).memberController_sender_eq
        false true word

/-- Process-two shared-control closure. -/
theorem
    profiledRawJointGuardedCommonLiteralStrictRightPostResolveJointTable_step_eq
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (control :
      ((profiledRawJointGuardedCommonLiteralStrictRightPostResolveJointTable
        A strategy hwin initial entry input).memberController false).Control)
    (own : In₂) :
    let table :=
      profiledRawJointGuardedCommonLiteralStrictRightPostResolveJointTable
        A strategy hwin initial entry input
    (table.memberController false).step control own =
      (table.memberController true).step control own := by
  dsimp only
  exact
    (profiledRawJointGuardedCommonLiteralStrictRightPostResolveJointTable
      A strategy hwin initial entry input).memberController_step_eq
        false true control own

/-! ## Globally finite post-resolve installation

The heterogeneous tables above are the semantic existence proof, but their
types still mention the exact occurrence.  We now erase both receiver target
types to the fixed finite incidence-code alphabet.  The exact strict target
is retained as a Boolean truth table together with its literal-child witness;
the common target is retained as the Boolean table of simultaneous semantic
successors.  Thus semantic histories occur only in the installation map, not
in the runtime move type. -/

/-! ### Process one -/

/-- Finite descriptor for the exact strict-left continuation.  Its truth
table remembers precisely the incidence codes occurring as exact
root-pinned literal children. -/
private noncomputable def strictLeftFiniteDescriptor
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    ProfiledRawJointRightPhysicalSiblingDescriptor A := by
  classical
  exact {
    source := StrictLeftSource A strategy initial entry input
    allowed := fun target ↦ decide (∃ row past nextInput,
      (profiledRawJointGuardedFirstRightTarget A strategy
        (StrictLeftChild A strategy initial entry input)
        (StrictLeftPredicate A strategy initial entry input)
        (StrictLeftPolicy A strategy hwin initial entry input)
        row past nextInput).1 = target) }

omit [DecidableEq In₁] [DecidableEq In₂] in
omit [Inhabited Out₁] [Inhabited Out₂] in
private theorem strictLeftFiniteDescriptor_allowed_iff
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (target : ProfiledRawJointUnitTarget A) :
    profiledRawJointRightPhysicalSiblingAllowed A
        (strictLeftFiniteDescriptor A strategy hwin initial entry input)
        target ↔
      ∃ row past nextInput,
        (profiledRawJointGuardedFirstRightTarget A strategy
          (StrictLeftChild A strategy initial entry input)
          (StrictLeftPredicate A strategy initial entry input)
          (StrictLeftPolicy A strategy hwin initial entry input)
          row past nextInput).1 = target := by
  simp [profiledRawJointRightPhysicalSiblingAllowed,
    strictLeftFiniteDescriptor]

/-- Finite descriptor for the simultaneous continuation paired with the
strict-left occurrence. -/
private noncomputable def commonAfterLeftFiniteDescriptor
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    ProfiledRawJointRightPhysicalSiblingDescriptor A := by
  classical
  exact {
    source := StrictLeftSource A strategy initial entry input
    allowed := fun target ↦ decide
      (ProfiledRawJointRightSiblingAllowedTarget A
        (strictLeftParent A strategy initial).family
        (strictLeftActual entry input).direction false target) }

omit [DecidableEq In₁] [DecidableEq In₂] in
omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] in
private theorem commonAfterLeftFiniteDescriptor_allowed_iff
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (target : ProfiledRawJointUnitTarget A) :
    profiledRawJointRightPhysicalSiblingAllowed A
        (commonAfterLeftFiniteDescriptor A strategy initial entry input)
        target ↔
      ProfiledRawJointRightSiblingAllowedTarget A
        (strictLeftParent A strategy initial).family
        (strictLeftActual entry input).direction false target := by
  simp [profiledRawJointRightPhysicalSiblingAllowed,
    commonAfterLeftFiniteDescriptor]

/-- Erase the dependent exact-child subtype while preserving its full
incidence code in the descriptor invariant. -/
private noncomputable def strictLeftFiniteActivation
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    ProfiledRawJointTargetRightBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitRightTargetProjection A)
      (profiledRawJointRightPhysicalSiblingAllowed A
        (strictLeftFiniteDescriptor A strategy hwin initial entry input))
      (strictLeftFiniteDescriptor A strategy hwin initial entry input).source := by
  classical
  let exact := strictLeftActivation A strategy hwin initial entry input
  refine {
    lambda := exact.lambda
    initial_profile := by
      simpa [strictLeftFiniteDescriptor] using exact.initial_profile
    forever := by
      simpa [strictLeftFiniteDescriptor] using exact.forever
    target := fun row past nextInput ↦
      (profiledRawJointGuardedFirstRightTarget A strategy
        (StrictLeftChild A strategy initial entry input)
        (StrictLeftPredicate A strategy initial entry input)
        (StrictLeftPolicy A strategy hwin initial entry input)
        row past nextInput).1
    target_allowed := ?_
    target_state := ?_ }
  · intro row past nextInput
    rw [strictLeftFiniteDescriptor_allowed_iff A strategy hwin]
    exact ⟨row, past, nextInput, rfl⟩
  · intro row past nextInput
    unfold profiledRawJointUnitRightTargetProjection
    rw [exact.target_active_slot row past nextInput]
    rfl

/-- Re-express the simultaneous semantic activation with its finite Boolean
descriptor. -/
private noncomputable def commonAfterLeftFiniteActivation
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    ProfiledRawJointTargetRightBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitRightTargetProjection A)
      (profiledRawJointRightPhysicalSiblingAllowed A
        (commonAfterLeftFiniteDescriptor A strategy initial entry input))
      (commonAfterLeftFiniteDescriptor A strategy initial entry input).source := by
  let base := profiledRawJointRightSiblingActivation A hwin
    (strictLeftParent A strategy initial).family
    (strictLeftActual entry input).direction
    (StrictLeftPair A strategy initial entry input)
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictLeftSemanticChild_live
      A strategy initial entry input) false
  refine {
    lambda := base.lambda
    initial_profile := base.initial_profile
    forever := base.forever
    target := base.target
    target_allowed := ?_
    target_state := base.target_state }
  intro row past nextInput
  rw [commonAfterLeftFiniteDescriptor_allowed_iff A strategy]
  exact base.target_allowed row past nextInput

private abbrev PostResolveRightMonitor
    (descriptor : ProfiledRawJointRightPhysicalSiblingDescriptor A) :=
  profiledRawJointRightPhysicalSiblingMonitor A descriptor false

/-- Public runtime monitor family for the process-one post-resolve move.
The semantic installation data has already been compressed into `descriptor`. -/
abbrev profiledRawJointStrictLeftPostResolveFiniteMonitor
    (descriptor : ProfiledRawJointRightPhysicalSiblingDescriptor A) :=
  PostResolveRightMonitor A descriptor

/-- The runtime move alphabet for process one.  This type depends only on
the automaton and the four finite input/output alphabets; no semantic history,
world, child, or policy occurs in it. -/
noncomputable abbrev ProfiledRawJointStrictLeftPostResolveFiniteMove :=
  FiniteCrossAnchorDescriptorMove (PostResolveRightMonitor A)

noncomputable instance :
    Fintype (ProfiledRawJointStrictLeftPostResolveFiniteMove A) := by
  classical
  infer_instance

private noncomputable def strictLeftPostResolveDescriptorPair
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    FiniteCrossAnchorDescriptorPair (PostResolveRightMonitor A) := by
  let descriptor : Bool → ProfiledRawJointRightPhysicalSiblingDescriptor A :=
    fun member ↦ if member then
      commonAfterLeftFiniteDescriptor A strategy initial entry input
    else strictLeftFiniteDescriptor A strategy hwin initial entry input
  exact {
    descriptor := descriptor
    start := fun member ↦
      (PostResolveRightMonitor A (descriptor member)).initial }

private def strictLeftPostResolveReceiver
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) :
    ReceiverBlockStrategy In₂ In₁
      (ProfiledRawJointTargetRightReceiverOutput
        (Out₁ := Out₁) (Out₂ := Out₂)
        (ProfiledRawJointUnitTarget A)) :=
  if member then
    profiledRawJointTargetRightReceiverStrategy A
      (commonAfterLeftFiniteActivation A strategy hwin initial entry input)
  else
    profiledRawJointTargetRightReceiverStrategy A
      (strictLeftFiniteActivation A strategy hwin initial entry input)

omit [Inhabited Out₁] [Inhabited Out₂] in
private theorem strictLeftPostResolve_realizable
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    ∀ member env,
      ((PostResolveRightMonitor A
          ((strictLeftPostResolveDescriptorPair A strategy hwin initial entry
            input).descriptor member)).restartAt
        ((strictLeftPostResolveDescriptorPair A strategy hwin initial entry
          input).start member)).WinsPlay
        (pairPlay
          (strictLeftPostResolveReceiver A strategy hwin initial entry input
            member)
          (pairedRightSenderStrategy
            (StrictLeftPair A strategy initial entry input).1.lambdaOfStrategy)
          env) := by
  intro member env
  cases member with
  | false =>
      have hreal := profiledRawJointTargetRightBlockMonitor_realizable A
        (profiledRawJointUnitRightTargetProjection A)
        (profiledRawJointRightPhysicalSiblingAllowed A
          (strictLeftFiniteDescriptor A strategy hwin initial entry input))
        (strictLeftFiniteDescriptor A strategy hwin initial entry input).source
        (strictLeftFiniteActivation A strategy hwin initial entry input) env
      rw [← strictLeftActivation_lambda A strategy hwin initial entry input]
      simpa [strictLeftPostResolveDescriptorPair, PostResolveRightMonitor,
        strictLeftPostResolveReceiver, strictLeftFiniteActivation,
        BlockRecordMonitor.restartAt] using hreal
  | true =>
      have hreal := profiledRawJointTargetRightBlockMonitor_realizable A
        (profiledRawJointUnitRightTargetProjection A)
        (profiledRawJointRightPhysicalSiblingAllowed A
          (commonAfterLeftFiniteDescriptor A strategy initial entry input))
        (commonAfterLeftFiniteDescriptor A strategy initial entry input).source
        (commonAfterLeftFiniteActivation A strategy hwin initial entry input) env
      simpa [strictLeftPostResolveDescriptorPair, PostResolveRightMonitor,
        strictLeftPostResolveReceiver, profiledRawJointRightSiblingSender,
        BlockRecordMonitor.restartAt] using hreal

/-- Install one semantic post-resolve occurrence into the fixed finite move
alphabet.  `false` reads the strict literal-child invariant and `true` reads
the simultaneous semantic-successor invariant. -/
noncomputable def profiledRawJointStrictLeftPostResolveFiniteMove
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    ProfiledRawJointStrictLeftPostResolveFiniteMove A :=
  finiteCrossAnchorDescriptorMove (PostResolveRightMonitor A)
    (strictLeftPostResolveDescriptorPair A strategy hwin initial entry input)
    (strictLeftPostResolveReceiver A strategy hwin initial entry input)
    (pairedRightSenderStrategy
      (StrictLeftPair A strategy initial entry input).1.lambdaOfStrategy)
    (strictLeftPostResolve_realizable A strategy hwin initial entry input)

/-- Exact-child readback after an arbitrary blind prefix.  The narrowed
receiver may choose any exact literal child accepted by the installed truth
table; the witness below recovers the original root-pinned target that gave
that finite code. -/
theorem profiledRawJointStrictLeftPostResolveFiniteMove_strictTarget
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (env : Nat → In₂ × In₁) (n : Nat) (row : PairedEntryRow) :
    let move := profiledRawJointStrictLeftPostResolveFiniteMove A strategy hwin
      initial entry input
    let monitor := PostResolveRightMonitor A
      (strictLeftFiniteDescriptor A strategy hwin initial entry input)
    let controller := move.memberController (PostResolveRightMonitor A) false
    let play := treePlay
      (narrowedInducedTree monitor controller.labeledTree) env
    erasePairedProfiledState A
        (profiledRawJointUnitRightTargetProjection A
          ((play n).2.1.target row)) =
        pairedRightCloseTarget A ((monitor.run play n).2.1) row
          (profiledRawJointTargetRightPhysicalLetter A (play n)) ∧
      ∃ witnessRow past nextInput,
        (profiledRawJointGuardedFirstRightTarget A strategy
          (StrictLeftChild A strategy initial entry input)
          (StrictLeftPredicate A strategy initial entry input)
          (StrictLeftPolicy A strategy hwin initial entry input)
          witnessRow past nextInput).1 = (play n).2.1.target row := by
  dsimp only
  let move := profiledRawJointStrictLeftPostResolveFiniteMove A strategy hwin
    initial entry input
  let monitor := PostResolveRightMonitor A
    (strictLeftFiniteDescriptor A strategy hwin initial entry input)
  let controller := move.memberController (PostResolveRightMonitor A) false
  have hwins : NarrowedAllThreadsWin monitor controller.labeledTree := by
    simpa [move, monitor, controller,
      profiledRawJointStrictLeftPostResolveFiniteMove,
      strictLeftPostResolveDescriptorPair, PostResolveRightMonitor,
      BlockRecordMonitor.restartAt] using
      (move.2.memberController_wins false)
  have hsafe := profiledRawJointTargetRight_narrowedTargetSafe A
    (profiledRawJointUnitRightTargetProjection A)
    (profiledRawJointRightPhysicalSiblingAllowed A
      (strictLeftFiniteDescriptor A strategy hwin initial entry input))
    (strictLeftFiniteDescriptor A strategy hwin initial entry input).source
    controller.labeledTree hwins env n row
  exact ⟨hsafe.1,
    (strictLeftFiniteDescriptor_allowed_iff A strategy hwin initial entry
      input _).mp hsafe.2⟩

/-- Simultaneous-successor readback after an arbitrary blind prefix. -/
theorem profiledRawJointStrictLeftPostResolveFiniteMove_commonTarget
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (env : Nat → In₂ × In₁) (n : Nat) (row : PairedEntryRow) :
    let move := profiledRawJointStrictLeftPostResolveFiniteMove A strategy hwin
      initial entry input
    let monitor := PostResolveRightMonitor A
      (commonAfterLeftFiniteDescriptor A strategy initial entry input)
    let controller := move.memberController (PostResolveRightMonitor A) true
    let play := treePlay
      (narrowedInducedTree monitor controller.labeledTree) env
    erasePairedProfiledState A
        (profiledRawJointUnitRightTargetProjection A
          ((play n).2.1.target row)) =
        pairedRightCloseTarget A ((monitor.run play n).2.1) row
          (profiledRawJointTargetRightPhysicalLetter A (play n)) ∧
      ProfiledRawJointRightSiblingAllowedTarget A
        (strictLeftParent A strategy initial).family
        (strictLeftActual entry input).direction false
        ((play n).2.1.target row) := by
  dsimp only
  let move := profiledRawJointStrictLeftPostResolveFiniteMove A strategy hwin
    initial entry input
  let monitor := PostResolveRightMonitor A
    (commonAfterLeftFiniteDescriptor A strategy initial entry input)
  let controller := move.memberController (PostResolveRightMonitor A) true
  have hwins : NarrowedAllThreadsWin monitor controller.labeledTree := by
    simpa [move, monitor, controller,
      profiledRawJointStrictLeftPostResolveFiniteMove,
      strictLeftPostResolveDescriptorPair, PostResolveRightMonitor,
      BlockRecordMonitor.restartAt] using
      (move.2.memberController_wins true)
  have hsafe := profiledRawJointTargetRight_narrowedTargetSafe A
    (profiledRawJointUnitRightTargetProjection A)
    (profiledRawJointRightPhysicalSiblingAllowed A
      (commonAfterLeftFiniteDescriptor A strategy initial entry input))
    (commonAfterLeftFiniteDescriptor A strategy initial entry input).source
    controller.labeledTree hwins env n row
  exact ⟨hsafe.1,
    (commonAfterLeftFiniteDescriptor_allowed_iff A strategy initial entry input
      _).mp hsafe.2⟩

/-! ### Process two -/

/-- Finite truth table of exact strict-right literal-child codes. -/
private noncomputable def strictRightFiniteDescriptor
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    ProfiledRawJointLeftPhysicalSiblingDescriptor A := by
  classical
  exact {
    source := StrictRightSource A strategy initial entry input
    allowed := fun target ↦ decide (∃ row past nextInput,
      (profiledRawJointGuardedFirstLeftTarget A strategy
        (StrictRightChild A strategy initial entry input)
        (StrictRightPredicate A strategy initial entry input)
        (StrictRightPolicy A strategy hwin initial entry input)
        row past nextInput).1 = target) }

omit [DecidableEq In₁] [DecidableEq In₂] in
omit [Inhabited Out₁] [Inhabited Out₂] in
private theorem strictRightFiniteDescriptor_allowed_iff
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (target : ProfiledRawJointUnitTarget A) :
    profiledRawJointLeftPhysicalSiblingAllowed A
        (strictRightFiniteDescriptor A strategy hwin initial entry input)
        target ↔
      ∃ row past nextInput,
        (profiledRawJointGuardedFirstLeftTarget A strategy
          (StrictRightChild A strategy initial entry input)
          (StrictRightPredicate A strategy initial entry input)
          (StrictRightPolicy A strategy hwin initial entry input)
          row past nextInput).1 = target := by
  simp [profiledRawJointLeftPhysicalSiblingAllowed,
    strictRightFiniteDescriptor]

/-- Finite truth table of simultaneous successors paired with the
strict-right occurrence. -/
private noncomputable def commonAfterRightFiniteDescriptor
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    ProfiledRawJointLeftPhysicalSiblingDescriptor A := by
  classical
  exact {
    source := StrictRightSource A strategy initial entry input
    allowed := fun target ↦ decide
      (ProfiledRawJointLeftSiblingAllowedTarget A
        (strictRightParent A strategy initial).family
        (strictRightActual entry input).direction false target) }

omit [DecidableEq In₁] [DecidableEq In₂] in
omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] in
private theorem commonAfterRightFiniteDescriptor_allowed_iff
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (target : ProfiledRawJointUnitTarget A) :
    profiledRawJointLeftPhysicalSiblingAllowed A
        (commonAfterRightFiniteDescriptor A strategy initial entry input)
        target ↔
      ProfiledRawJointLeftSiblingAllowedTarget A
        (strictRightParent A strategy initial).family
        (strictRightActual entry input).direction false target := by
  simp [profiledRawJointLeftPhysicalSiblingAllowed,
    commonAfterRightFiniteDescriptor]

/-- Uniform finite-target activation for the exact strict-right child. -/
private noncomputable def strictRightFiniteActivation
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    ProfiledRawJointTargetLeftBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitLeftTargetProjection A)
      (profiledRawJointLeftPhysicalSiblingAllowed A
        (strictRightFiniteDescriptor A strategy hwin initial entry input))
      (strictRightFiniteDescriptor A strategy hwin initial entry input).source := by
  classical
  let exact := strictRightActivation A strategy hwin initial entry input
  refine {
    lambda := exact.lambda
    initial_profile := by
      simpa [strictRightFiniteDescriptor] using exact.initial_profile
    forever := by
      simpa [strictRightFiniteDescriptor] using exact.forever
    target := fun row past nextInput ↦
      (profiledRawJointGuardedFirstLeftTarget A strategy
        (StrictRightChild A strategy initial entry input)
        (StrictRightPredicate A strategy initial entry input)
        (StrictRightPolicy A strategy hwin initial entry input)
        row past nextInput).1
    target_allowed := ?_
    target_state := ?_ }
  · intro row past nextInput
    rw [strictRightFiniteDescriptor_allowed_iff A strategy hwin]
    exact ⟨row, past, nextInput, rfl⟩
  · intro row past nextInput
    unfold profiledRawJointUnitLeftTargetProjection
    rw [exact.target_active_slot row past nextInput]
    rfl

/-- Uniform finite-target activation for the simultaneous mirror. -/
private noncomputable def commonAfterRightFiniteActivation
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    ProfiledRawJointTargetLeftBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitLeftTargetProjection A)
      (profiledRawJointLeftPhysicalSiblingAllowed A
        (commonAfterRightFiniteDescriptor A strategy initial entry input))
      (commonAfterRightFiniteDescriptor A strategy initial entry input).source := by
  let base := profiledRawJointLeftSiblingActivation A hwin
    (strictRightParent A strategy initial).family
    (strictRightActual entry input).direction
    (StrictRightPair A strategy initial entry input)
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictRightSemanticChild_live
      A strategy initial entry input) false
  refine {
    lambda := base.lambda
    initial_profile := base.initial_profile
    forever := base.forever
    target := base.target
    target_allowed := ?_
    target_state := base.target_state }
  intro row past nextInput
  rw [commonAfterRightFiniteDescriptor_allowed_iff A strategy]
  exact base.target_allowed row past nextInput

private abbrev PostResolveLeftMonitor
    (descriptor : ProfiledRawJointLeftPhysicalSiblingDescriptor A) :=
  profiledRawJointLeftPhysicalSiblingMonitor A descriptor false

/-- Public runtime monitor family for the process-two mirror. -/
abbrev profiledRawJointStrictRightPostResolveFiniteMonitor
    (descriptor : ProfiledRawJointLeftPhysicalSiblingDescriptor A) :=
  PostResolveLeftMonitor A descriptor

/-- Globally finite process-two post-resolve move alphabet. -/
noncomputable abbrev ProfiledRawJointStrictRightPostResolveFiniteMove :=
  FiniteCrossAnchorDescriptorMove (PostResolveLeftMonitor A)

noncomputable instance :
    Fintype (ProfiledRawJointStrictRightPostResolveFiniteMove A) := by
  classical
  infer_instance

private noncomputable def strictRightPostResolveDescriptorPair
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    FiniteCrossAnchorDescriptorPair (PostResolveLeftMonitor A) := by
  let descriptor : Bool → ProfiledRawJointLeftPhysicalSiblingDescriptor A :=
    fun member ↦ if member then
      commonAfterRightFiniteDescriptor A strategy initial entry input
    else strictRightFiniteDescriptor A strategy hwin initial entry input
  exact {
    descriptor := descriptor
    start := fun member ↦
      (PostResolveLeftMonitor A (descriptor member)).initial }

private def strictRightPostResolveReceiver
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) :
    ReceiverBlockStrategy In₁ In₂
      (ProfiledRawJointTargetLeftReceiverOutput
        (Out₁ := Out₁) (Out₂ := Out₂)
        (ProfiledRawJointUnitTarget A)) :=
  if member then
    profiledRawJointTargetLeftReceiverStrategy A
      (commonAfterRightFiniteActivation A strategy hwin initial entry input)
  else
    profiledRawJointTargetLeftReceiverStrategy A
      (strictRightFiniteActivation A strategy hwin initial entry input)

omit [Inhabited Out₁] [Inhabited Out₂] in
private theorem strictRightPostResolve_realizable
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    ∀ member env,
      ((PostResolveLeftMonitor A
          ((strictRightPostResolveDescriptorPair A strategy hwin initial entry
            input).descriptor member)).restartAt
        ((strictRightPostResolveDescriptorPair A strategy hwin initial entry
          input).start member)).WinsPlay
        (pairPlay
          (strictRightPostResolveReceiver A strategy hwin initial entry input
            member)
          (pairedLeftSenderStrategy
            (StrictRightPair A strategy initial entry input).1.lambdaOfStrategy)
          env) := by
  intro member env
  cases member with
  | false =>
      have hreal := profiledRawJointTargetLeftBlockMonitor_realizable A
        (profiledRawJointUnitLeftTargetProjection A)
        (profiledRawJointLeftPhysicalSiblingAllowed A
          (strictRightFiniteDescriptor A strategy hwin initial entry input))
        (strictRightFiniteDescriptor A strategy hwin initial entry input).source
        (strictRightFiniteActivation A strategy hwin initial entry input) env
      rw [← strictRightActivation_lambda A strategy hwin initial entry input]
      simpa [strictRightPostResolveDescriptorPair, PostResolveLeftMonitor,
        strictRightPostResolveReceiver, strictRightFiniteActivation,
        BlockRecordMonitor.restartAt] using hreal
  | true =>
      have hreal := profiledRawJointTargetLeftBlockMonitor_realizable A
        (profiledRawJointUnitLeftTargetProjection A)
        (profiledRawJointLeftPhysicalSiblingAllowed A
          (commonAfterRightFiniteDescriptor A strategy initial entry input))
        (commonAfterRightFiniteDescriptor A strategy initial entry input).source
        (commonAfterRightFiniteActivation A strategy hwin initial entry input) env
      simpa [strictRightPostResolveDescriptorPair, PostResolveLeftMonitor,
        strictRightPostResolveReceiver, profiledRawJointLeftSiblingSender,
        BlockRecordMonitor.restartAt] using hreal

/-- Install one process-two post-resolve occurrence into its fixed alphabet. -/
noncomputable def profiledRawJointStrictRightPostResolveFiniteMove
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    ProfiledRawJointStrictRightPostResolveFiniteMove A :=
  finiteCrossAnchorDescriptorMove (PostResolveLeftMonitor A)
    (strictRightPostResolveDescriptorPair A strategy hwin initial entry input)
    (strictRightPostResolveReceiver A strategy hwin initial entry input)
    (pairedLeftSenderStrategy
      (StrictRightPair A strategy initial entry input).1.lambdaOfStrategy)
    (strictRightPostResolve_realizable A strategy hwin initial entry input)

/-- Strict-right exact-child readback after any finite blind prefix. -/
theorem profiledRawJointStrictRightPostResolveFiniteMove_strictTarget
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (env : Nat → In₁ × In₂) (n : Nat) (row : PairedEntryRow) :
    let move := profiledRawJointStrictRightPostResolveFiniteMove A strategy hwin
      initial entry input
    let monitor := PostResolveLeftMonitor A
      (strictRightFiniteDescriptor A strategy hwin initial entry input)
    let controller := move.memberController (PostResolveLeftMonitor A) false
    let play := treePlay
      (narrowedInducedTree monitor controller.labeledTree) env
    erasePairedProfiledState A
        (profiledRawJointUnitLeftTargetProjection A
          ((play n).2.1.target row)) =
        pairedLeftCloseTarget A ((monitor.run play n).2.1) row
          (profiledRawJointTargetLeftPhysicalLetter A (play n)) ∧
      ∃ witnessRow past nextInput,
        (profiledRawJointGuardedFirstLeftTarget A strategy
          (StrictRightChild A strategy initial entry input)
          (StrictRightPredicate A strategy initial entry input)
          (StrictRightPolicy A strategy hwin initial entry input)
          witnessRow past nextInput).1 = (play n).2.1.target row := by
  dsimp only
  let move := profiledRawJointStrictRightPostResolveFiniteMove A strategy hwin
    initial entry input
  let monitor := PostResolveLeftMonitor A
    (strictRightFiniteDescriptor A strategy hwin initial entry input)
  let controller := move.memberController (PostResolveLeftMonitor A) false
  have hwins : NarrowedAllThreadsWin monitor controller.labeledTree := by
    simpa [move, monitor, controller,
      profiledRawJointStrictRightPostResolveFiniteMove,
      strictRightPostResolveDescriptorPair, PostResolveLeftMonitor,
      BlockRecordMonitor.restartAt] using
      (move.2.memberController_wins false)
  have hsafe := profiledRawJointTargetLeft_narrowedTargetSafe A
    (profiledRawJointUnitLeftTargetProjection A)
    (profiledRawJointLeftPhysicalSiblingAllowed A
      (strictRightFiniteDescriptor A strategy hwin initial entry input))
    (strictRightFiniteDescriptor A strategy hwin initial entry input).source
    controller.labeledTree hwins env n row
  exact ⟨hsafe.1,
    (strictRightFiniteDescriptor_allowed_iff A strategy hwin initial entry
      input _).mp hsafe.2⟩

/-- Simultaneous mirror readback after any finite blind prefix. -/
theorem profiledRawJointStrictRightPostResolveFiniteMove_commonTarget
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (env : Nat → In₁ × In₂) (n : Nat) (row : PairedEntryRow) :
    let move := profiledRawJointStrictRightPostResolveFiniteMove A strategy hwin
      initial entry input
    let monitor := PostResolveLeftMonitor A
      (commonAfterRightFiniteDescriptor A strategy initial entry input)
    let controller := move.memberController (PostResolveLeftMonitor A) true
    let play := treePlay
      (narrowedInducedTree monitor controller.labeledTree) env
    erasePairedProfiledState A
        (profiledRawJointUnitLeftTargetProjection A
          ((play n).2.1.target row)) =
        pairedLeftCloseTarget A ((monitor.run play n).2.1) row
          (profiledRawJointTargetLeftPhysicalLetter A (play n)) ∧
      ProfiledRawJointLeftSiblingAllowedTarget A
        (strictRightParent A strategy initial).family
        (strictRightActual entry input).direction false
        ((play n).2.1.target row) := by
  dsimp only
  let move := profiledRawJointStrictRightPostResolveFiniteMove A strategy hwin
    initial entry input
  let monitor := PostResolveLeftMonitor A
    (commonAfterRightFiniteDescriptor A strategy initial entry input)
  let controller := move.memberController (PostResolveLeftMonitor A) true
  have hwins : NarrowedAllThreadsWin monitor controller.labeledTree := by
    simpa [move, monitor, controller,
      profiledRawJointStrictRightPostResolveFiniteMove,
      strictRightPostResolveDescriptorPair, PostResolveLeftMonitor,
      BlockRecordMonitor.restartAt] using
      (move.2.memberController_wins true)
  have hsafe := profiledRawJointTargetLeft_narrowedTargetSafe A
    (profiledRawJointUnitLeftTargetProjection A)
    (profiledRawJointLeftPhysicalSiblingAllowed A
      (commonAfterRightFiniteDescriptor A strategy initial entry input))
    (commonAfterRightFiniteDescriptor A strategy initial entry input).source
    controller.labeledTree hwins env n row
  exact ⟨hsafe.1,
    (commonAfterRightFiniteDescriptor_allowed_iff A strategy initial entry input
      _).mp hsafe.2⟩

/-! ### Uniform member readback interfaces -/

/-- Proof-side meaning of a target emitted by the process-one finite move.
`false` means an exact target of the root-pinned strict-left child; `true`
means a literal successor of the simultaneous semantic child. -/
def ProfiledRawJointStrictLeftPostResolveFiniteTargetMeaning
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (branch : Bool) (target : ProfiledRawJointUnitTarget A) : Prop :=
  match branch with
  | false =>
      ∃ witnessRow past nextInput,
        (profiledRawJointGuardedFirstRightTarget A strategy
          (StrictLeftChild A strategy initial entry input)
          (StrictLeftPredicate A strategy initial entry input)
          (StrictLeftPolicy A strategy hwin initial entry input)
          witnessRow past nextInput).1 = target
  | true =>
      ProfiledRawJointRightSiblingAllowedTarget A
        (strictLeftParent A strategy initial).family
        (strictLeftActual entry input).direction false target

/-- Proof-side meaning of a target emitted by the mirrored process-two move. -/
def ProfiledRawJointStrictRightPostResolveFiniteTargetMeaning
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (branch : Bool) (target : ProfiledRawJointUnitTarget A) : Prop :=
  match branch with
  | false =>
      ∃ witnessRow past nextInput,
        (profiledRawJointGuardedFirstLeftTarget A strategy
          (StrictRightChild A strategy initial entry input)
          (StrictRightPredicate A strategy initial entry input)
          (StrictRightPolicy A strategy hwin initial entry input)
          witnessRow past nextInput).1 = target
  | true =>
      ProfiledRawJointLeftSiblingAllowedTarget A
        (strictRightParent A strategy initial).family
        (strictRightActual entry input).direction false target

/-- One theorem covers both stored members of the process-one runtime move.
It is the public interface used by a receive dispatcher, which reads the
member from local receiver state rather than branching on the current graph. -/
theorem profiledRawJointStrictLeftPostResolveFiniteMove_targetMeaning
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (branch : Bool) (env : Nat → In₂ × In₁) (n : Nat)
    (row : PairedEntryRow) :
    let move := profiledRawJointStrictLeftPostResolveFiniteMove A strategy hwin
      initial entry input
    let monitor := (profiledRawJointStrictLeftPostResolveFiniteMonitor A
      (move.1.descriptor branch)).restartAt (move.1.start branch)
    let controller := move.memberController
      (profiledRawJointStrictLeftPostResolveFiniteMonitor A) branch
    let play := treePlay
      (narrowedInducedTree monitor controller.labeledTree) env
    erasePairedProfiledState A
        (profiledRawJointUnitRightTargetProjection A
          ((play n).2.1.target row)) =
        pairedRightCloseTarget A ((monitor.run play n).2.1) row
          (profiledRawJointTargetRightPhysicalLetter A (play n)) ∧
      ProfiledRawJointStrictLeftPostResolveFiniteTargetMeaning A strategy hwin
        initial entry input branch ((play n).2.1.target row) := by
  cases branch with
  | false =>
      simpa [ProfiledRawJointStrictLeftPostResolveFiniteTargetMeaning,
        profiledRawJointStrictLeftPostResolveFiniteMove,
        strictLeftPostResolveDescriptorPair,
        profiledRawJointStrictLeftPostResolveFiniteMonitor,
        PostResolveRightMonitor, BlockRecordMonitor.restartAt] using
        (profiledRawJointStrictLeftPostResolveFiniteMove_strictTarget A
          strategy hwin initial entry input env n row)
  | true =>
      simpa [ProfiledRawJointStrictLeftPostResolveFiniteTargetMeaning,
        profiledRawJointStrictLeftPostResolveFiniteMove,
        strictLeftPostResolveDescriptorPair,
        profiledRawJointStrictLeftPostResolveFiniteMonitor,
        PostResolveRightMonitor, BlockRecordMonitor.restartAt] using
        (profiledRawJointStrictLeftPostResolveFiniteMove_commonTarget A
          strategy hwin initial entry input env n row)

/-- Uniform stored-member readback for the mirrored process-two move. -/
theorem profiledRawJointStrictRightPostResolveFiniteMove_targetMeaning
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (branch : Bool) (env : Nat → In₁ × In₂) (n : Nat)
    (row : PairedEntryRow) :
    let move := profiledRawJointStrictRightPostResolveFiniteMove A strategy hwin
      initial entry input
    let monitor := (profiledRawJointStrictRightPostResolveFiniteMonitor A
      (move.1.descriptor branch)).restartAt (move.1.start branch)
    let controller := move.memberController
      (profiledRawJointStrictRightPostResolveFiniteMonitor A) branch
    let play := treePlay
      (narrowedInducedTree monitor controller.labeledTree) env
    erasePairedProfiledState A
        (profiledRawJointUnitLeftTargetProjection A
          ((play n).2.1.target row)) =
        pairedLeftCloseTarget A ((monitor.run play n).2.1) row
          (profiledRawJointTargetLeftPhysicalLetter A (play n)) ∧
      ProfiledRawJointStrictRightPostResolveFiniteTargetMeaning A strategy hwin
        initial entry input branch ((play n).2.1.target row) := by
  cases branch with
  | false =>
      simpa [ProfiledRawJointStrictRightPostResolveFiniteTargetMeaning,
        profiledRawJointStrictRightPostResolveFiniteMove,
        strictRightPostResolveDescriptorPair,
        profiledRawJointStrictRightPostResolveFiniteMonitor,
        PostResolveLeftMonitor, BlockRecordMonitor.restartAt] using
        (profiledRawJointStrictRightPostResolveFiniteMove_strictTarget A
          strategy hwin initial entry input env n row)
  | true =>
      simpa [ProfiledRawJointStrictRightPostResolveFiniteTargetMeaning,
        profiledRawJointStrictRightPostResolveFiniteMove,
        strictRightPostResolveDescriptorPair,
        profiledRawJointStrictRightPostResolveFiniteMonitor,
        PostResolveLeftMonitor, BlockRecordMonitor.restartAt] using
        (profiledRawJointStrictRightPostResolveFiniteMove_commonTarget A
          strategy hwin initial entry input env n row)

/-! ### Conversion to the existing fixed-policy continuation -/

omit [DecidableEq In₁] [DecidableEq In₂] in
omit [Inhabited Out₁] [Inhabited Out₂] in
/-- An exact strict-left target, together with its physical close equation,
starts one fresh recurrent policy at the exact literal semantic child. -/
theorem
    nonempty_profiledRawJointStrictLeftPostResolveFiniteFreshPolicyPackage_of_strictTarget
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (target : ProfiledRawJointUnitTarget A)
    (htarget : ProfiledRawJointStrictLeftPostResolveFiniteTargetMeaning A
      strategy hwin initial entry input false target)
    (scan : PairedRightScanState A) (row : PairedEntryRow)
    (physical : PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hclose : erasePairedProfiledState A
        (profiledRawJointUnitRightTargetProjection A target) =
      pairedRightCloseTarget A scan row physical) :
    Nonempty (ProfiledRawJointSiblingFreshPolicyPackage A strategy target) := by
  classical
  change (∃ witnessRow past nextInput,
    (profiledRawJointGuardedFirstRightTarget A strategy
      (StrictLeftChild A strategy initial entry input)
      (StrictLeftPredicate A strategy initial entry input)
      (StrictLeftPolicy A strategy hwin initial entry input)
      witnessRow past nextInput).1 = target) at htarget
  rcases htarget with ⟨witnessRow, past, nextInput, htarget⟩
  subst target
  let strictInitial := StrictLeftChild A strategy initial entry input
  let predicate := StrictLeftPredicate A strategy initial entry input
  let rootPolicy := StrictLeftPolicy A strategy hwin initial entry input
  let selected := profiledRawJointRootPinnedSelectedSource A strategy
    strictInitial predicate rootPolicy
  let child := profiledRawJointGuardedFirstRightTarget A strategy strictInitial
    predicate rootPolicy witnessRow past nextInput
  let childSource := profiledRawJointOneSidedLiteralChildSource A strategy
    selected child
  have hcode : childSource.code A = child.1 :=
    profiledRawJointOneSidedLiteralChildSource_code A strategy selected child
  let policy := Classical.choice
    (nonempty_profiledRawJointOneSidedProvenanceRationalPolicy A strategy hwin
      childSource)
  have hrootCode : (policy.run []).1 = childSource.code A :=
    congrArg Prod.fst policy.accepts.1.1
  change erasePairedProfiledState A
      (profiledRawJointUnitRightTargetProjection A child.1) =
    pairedRightCloseTarget A scan row physical at hclose
  cases hslot : child.1.family.left () with
  | none =>
      simp [profiledRawJointUnitRightTargetProjection, hslot,
        erasePairedProfiledState, pairedRightCloseTarget] at hclose
  | some slot =>
      let seed : ProfiledRawJointUnitLeftPolicyMacro A strategy
          (childSource.code A) policy := {
        state := policy.run []
        reachable := ⟨[], rfl⟩
        slot := slot
        active_slot := by
          rw [hrootCode, hcode, hslot] }
      exact ⟨⟨childSource, hcode, policy, .inr seed, rfl⟩⟩

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- The simultaneous process-one target uses the existing semantic-sibling
fresh-policy constructor. -/
theorem
    nonempty_profiledRawJointStrictLeftPostResolveFiniteFreshPolicyPackage_of_commonTarget
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (target : ProfiledRawJointUnitTarget A)
    (htarget : ProfiledRawJointStrictLeftPostResolveFiniteTargetMeaning A
      strategy hwin initial entry input true target)
    (scan : PairedRightScanState A) (row : PairedEntryRow)
    (physical : PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hclose : erasePairedProfiledState A
        (profiledRawJointUnitRightTargetProjection A target) =
      pairedRightCloseTarget A scan row physical) :
    Nonempty (ProfiledRawJointSiblingFreshPolicyPackage A strategy target) := by
  exact nonempty_profiledRawJointRightSiblingFreshPolicyPackage_of_close A
    hwin (strictLeftParent A strategy initial).family
      (strictLeftActual entry input).direction target htarget scan row physical
        hclose

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Both stored process-one members feed the same fixed-policy continuation
interface. -/
theorem
    nonempty_profiledRawJointStrictLeftPostResolveFiniteFreshPolicyPackage_of_targetMeaning
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (branch : Bool) (target : ProfiledRawJointUnitTarget A)
    (htarget : ProfiledRawJointStrictLeftPostResolveFiniteTargetMeaning A
      strategy hwin initial entry input branch target)
    (scan : PairedRightScanState A) (row : PairedEntryRow)
    (physical : PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hclose : erasePairedProfiledState A
        (profiledRawJointUnitRightTargetProjection A target) =
      pairedRightCloseTarget A scan row physical) :
    Nonempty (ProfiledRawJointSiblingFreshPolicyPackage A strategy target) := by
  cases branch with
  | false =>
      exact
        nonempty_profiledRawJointStrictLeftPostResolveFiniteFreshPolicyPackage_of_strictTarget
          A strategy hwin initial entry input target htarget scan row physical
            hclose
  | true =>
      exact
        nonempty_profiledRawJointStrictLeftPostResolveFiniteFreshPolicyPackage_of_commonTarget
          A strategy hwin initial entry input target htarget scan row physical
            hclose

omit [DecidableEq In₁] [DecidableEq In₂] in
omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Mirrored exact strict-right conversion. -/
theorem
    nonempty_profiledRawJointStrictRightPostResolveFiniteFreshPolicyPackage_of_strictTarget
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (target : ProfiledRawJointUnitTarget A)
    (htarget : ProfiledRawJointStrictRightPostResolveFiniteTargetMeaning A
      strategy hwin initial entry input false target)
    (scan : PairedLeftScanState A) (row : PairedEntryRow)
    (physical : PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hclose : erasePairedProfiledState A
        (profiledRawJointUnitLeftTargetProjection A target) =
      pairedLeftCloseTarget A scan row physical) :
    Nonempty (ProfiledRawJointSiblingFreshPolicyPackage A strategy target) := by
  classical
  change (∃ witnessRow past nextInput,
    (profiledRawJointGuardedFirstLeftTarget A strategy
      (StrictRightChild A strategy initial entry input)
      (StrictRightPredicate A strategy initial entry input)
      (StrictRightPolicy A strategy hwin initial entry input)
      witnessRow past nextInput).1 = target) at htarget
  rcases htarget with ⟨witnessRow, past, nextInput, htarget⟩
  subst target
  let strictInitial := StrictRightChild A strategy initial entry input
  let predicate := StrictRightPredicate A strategy initial entry input
  let rootPolicy := StrictRightPolicy A strategy hwin initial entry input
  let selected := profiledRawJointRootPinnedSelectedSource A strategy
    strictInitial predicate rootPolicy
  let child := profiledRawJointGuardedFirstLeftTarget A strategy strictInitial
    predicate rootPolicy witnessRow past nextInput
  let childSource := profiledRawJointOneSidedLiteralChildSource A strategy
    selected child
  have hcode : childSource.code A = child.1 :=
    profiledRawJointOneSidedLiteralChildSource_code A strategy selected child
  let policy := Classical.choice
    (nonempty_profiledRawJointOneSidedProvenanceRationalPolicy A strategy hwin
      childSource)
  have hrootCode : (policy.run []).1 = childSource.code A :=
    congrArg Prod.fst policy.accepts.1.1
  change erasePairedProfiledState A
      (profiledRawJointUnitLeftTargetProjection A child.1) =
    pairedLeftCloseTarget A scan row physical at hclose
  cases hslot : child.1.family.right () with
  | none =>
      simp [profiledRawJointUnitLeftTargetProjection, hslot,
        erasePairedProfiledState, pairedLeftCloseTarget] at hclose
  | some slot =>
      let seed : ProfiledRawJointUnitRightPolicyMacro A strategy
          (childSource.code A) policy := {
        state := policy.run []
        reachable := ⟨[], rfl⟩
        slot := slot
        active_slot := by
          rw [hrootCode, hcode, hslot] }
      exact ⟨⟨childSource, hcode, policy, .inl seed, rfl⟩⟩

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Mirrored simultaneous conversion. -/
theorem
    nonempty_profiledRawJointStrictRightPostResolveFiniteFreshPolicyPackage_of_commonTarget
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (target : ProfiledRawJointUnitTarget A)
    (htarget : ProfiledRawJointStrictRightPostResolveFiniteTargetMeaning A
      strategy hwin initial entry input true target)
    (scan : PairedLeftScanState A) (row : PairedEntryRow)
    (physical : PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hclose : erasePairedProfiledState A
        (profiledRawJointUnitLeftTargetProjection A target) =
      pairedLeftCloseTarget A scan row physical) :
    Nonempty (ProfiledRawJointSiblingFreshPolicyPackage A strategy target) := by
  exact nonempty_profiledRawJointLeftSiblingFreshPolicyPackage_of_close A
    hwin (strictRightParent A strategy initial).family
      (strictRightActual entry input).direction target htarget scan row physical
        hclose

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Both mirrored members feed the fixed-policy continuation interface. -/
theorem
    nonempty_profiledRawJointStrictRightPostResolveFiniteFreshPolicyPackage_of_targetMeaning
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (branch : Bool) (target : ProfiledRawJointUnitTarget A)
    (htarget : ProfiledRawJointStrictRightPostResolveFiniteTargetMeaning A
      strategy hwin initial entry input branch target)
    (scan : PairedLeftScanState A) (row : PairedEntryRow)
    (physical : PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hclose : erasePairedProfiledState A
        (profiledRawJointUnitLeftTargetProjection A target) =
      pairedLeftCloseTarget A scan row physical) :
    Nonempty (ProfiledRawJointSiblingFreshPolicyPackage A strategy target) := by
  cases branch with
  | false =>
      exact
        nonempty_profiledRawJointStrictRightPostResolveFiniteFreshPolicyPackage_of_strictTarget
          A strategy hwin initial entry input target htarget scan row physical
            hclose
  | true =>
      exact
        nonempty_profiledRawJointStrictRightPostResolveFiniteFreshPolicyPackage_of_commonTarget
          A strategy hwin initial entry input target htarget scan row physical
            hclose

/-! ### Orientation-refined conversion for a global recurrent bank -/

omit [DecidableEq In₁] [DecidableEq In₂] in
omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The strict member of the process-one table retains a left recurrent root,
not merely an unoriented fixed-policy root. -/
theorem
    nonempty_profiledRawJointStrictLeftPostResolveFiniteRightCloseFreshPolicyPackage_of_strictTarget
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (target : ProfiledRawJointUnitTarget A)
    (htarget : ProfiledRawJointStrictLeftPostResolveFiniteTargetMeaning A
      strategy hwin initial entry input false target)
    (scan : PairedRightScanState A) (row : PairedEntryRow)
    (physical : PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hclose : erasePairedProfiledState A
        (profiledRawJointUnitRightTargetProjection A target) =
      pairedRightCloseTarget A scan row physical) :
    Nonempty
      (ProfiledRawJointRightCloseFreshPolicyPackage A strategy target) := by
  classical
  change (∃ witnessRow past nextInput,
    (profiledRawJointGuardedFirstRightTarget A strategy
      (StrictLeftChild A strategy initial entry input)
      (StrictLeftPredicate A strategy initial entry input)
      (StrictLeftPolicy A strategy hwin initial entry input)
      witnessRow past nextInput).1 = target) at htarget
  rcases htarget with ⟨witnessRow, past, nextInput, htarget⟩
  subst target
  let strictInitial := StrictLeftChild A strategy initial entry input
  let predicate := StrictLeftPredicate A strategy initial entry input
  let rootPolicy := StrictLeftPolicy A strategy hwin initial entry input
  let selected := profiledRawJointRootPinnedSelectedSource A strategy
    strictInitial predicate rootPolicy
  let child := profiledRawJointGuardedFirstRightTarget A strategy strictInitial
    predicate rootPolicy witnessRow past nextInput
  let childSource := profiledRawJointOneSidedLiteralChildSource A strategy
    selected child
  have hcode : childSource.code A = child.1 :=
    profiledRawJointOneSidedLiteralChildSource_code A strategy selected child
  let policy := Classical.choice
    (nonempty_profiledRawJointOneSidedProvenanceRationalPolicy A strategy hwin
      childSource)
  have hrootCode : (policy.run []).1 = childSource.code A :=
    congrArg Prod.fst policy.accepts.1.1
  change erasePairedProfiledState A
      (profiledRawJointUnitRightTargetProjection A child.1) =
    pairedRightCloseTarget A scan row physical at hclose
  cases hslot : child.1.family.left () with
  | none =>
      simp [profiledRawJointUnitRightTargetProjection, hslot,
        erasePairedProfiledState, pairedRightCloseTarget] at hclose
  | some slot =>
      let seed : ProfiledRawJointUnitLeftPolicyMacro A strategy
          (childSource.code A) policy := {
        state := policy.run []
        reachable := ⟨[], rfl⟩
        slot := slot
        active_slot := by
          rw [hrootCode, hcode, hslot] }
      exact ⟨⟨childSource, hcode, policy, seed, rfl⟩⟩

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- The simultaneous member has the same right-close orientation. -/
theorem
    nonempty_profiledRawJointStrictLeftPostResolveFiniteRightCloseFreshPolicyPackage_of_commonTarget
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (target : ProfiledRawJointUnitTarget A)
    (htarget : ProfiledRawJointStrictLeftPostResolveFiniteTargetMeaning A
      strategy hwin initial entry input true target)
    (scan : PairedRightScanState A) (row : PairedEntryRow)
    (physical : PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hclose : erasePairedProfiledState A
        (profiledRawJointUnitRightTargetProjection A target) =
      pairedRightCloseTarget A scan row physical) :
    Nonempty
      (ProfiledRawJointRightCloseFreshPolicyPackage A strategy target) := by
  exact nonempty_profiledRawJointRightCloseFreshPolicyPackage_of_close A hwin
    (strictLeftParent A strategy initial).family
      (strictLeftActual entry input).direction target htarget scan row physical
        hclose

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Either stored member of the process-one table supplies an explicitly
left-oriented recurrent root. -/
theorem
    nonempty_profiledRawJointStrictLeftPostResolveFiniteRightCloseFreshPolicyPackage_of_targetMeaning
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (branch : Bool) (target : ProfiledRawJointUnitTarget A)
    (htarget : ProfiledRawJointStrictLeftPostResolveFiniteTargetMeaning A
      strategy hwin initial entry input branch target)
    (scan : PairedRightScanState A) (row : PairedEntryRow)
    (physical : PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hclose : erasePairedProfiledState A
        (profiledRawJointUnitRightTargetProjection A target) =
      pairedRightCloseTarget A scan row physical) :
    Nonempty
      (ProfiledRawJointRightCloseFreshPolicyPackage A strategy target) := by
  cases branch with
  | false =>
      exact
        nonempty_profiledRawJointStrictLeftPostResolveFiniteRightCloseFreshPolicyPackage_of_strictTarget
          A strategy hwin initial entry input target htarget scan row physical
            hclose
  | true =>
      exact
        nonempty_profiledRawJointStrictLeftPostResolveFiniteRightCloseFreshPolicyPackage_of_commonTarget
          A strategy hwin initial entry input target htarget scan row physical
            hclose

omit [DecidableEq In₁] [DecidableEq In₂] in
omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The strict member of the mirrored process-two table retains a right
recurrent root. -/
theorem
    nonempty_profiledRawJointStrictRightPostResolveFiniteLeftCloseFreshPolicyPackage_of_strictTarget
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (target : ProfiledRawJointUnitTarget A)
    (htarget : ProfiledRawJointStrictRightPostResolveFiniteTargetMeaning A
      strategy hwin initial entry input false target)
    (scan : PairedLeftScanState A) (row : PairedEntryRow)
    (physical : PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hclose : erasePairedProfiledState A
        (profiledRawJointUnitLeftTargetProjection A target) =
      pairedLeftCloseTarget A scan row physical) :
    Nonempty
      (ProfiledRawJointLeftCloseFreshPolicyPackage A strategy target) := by
  classical
  change (∃ witnessRow past nextInput,
    (profiledRawJointGuardedFirstLeftTarget A strategy
      (StrictRightChild A strategy initial entry input)
      (StrictRightPredicate A strategy initial entry input)
      (StrictRightPolicy A strategy hwin initial entry input)
      witnessRow past nextInput).1 = target) at htarget
  rcases htarget with ⟨witnessRow, past, nextInput, htarget⟩
  subst target
  let strictInitial := StrictRightChild A strategy initial entry input
  let predicate := StrictRightPredicate A strategy initial entry input
  let rootPolicy := StrictRightPolicy A strategy hwin initial entry input
  let selected := profiledRawJointRootPinnedSelectedSource A strategy
    strictInitial predicate rootPolicy
  let child := profiledRawJointGuardedFirstLeftTarget A strategy strictInitial
    predicate rootPolicy witnessRow past nextInput
  let childSource := profiledRawJointOneSidedLiteralChildSource A strategy
    selected child
  have hcode : childSource.code A = child.1 :=
    profiledRawJointOneSidedLiteralChildSource_code A strategy selected child
  let policy := Classical.choice
    (nonempty_profiledRawJointOneSidedProvenanceRationalPolicy A strategy hwin
      childSource)
  have hrootCode : (policy.run []).1 = childSource.code A :=
    congrArg Prod.fst policy.accepts.1.1
  change erasePairedProfiledState A
      (profiledRawJointUnitLeftTargetProjection A child.1) =
    pairedLeftCloseTarget A scan row physical at hclose
  cases hslot : child.1.family.right () with
  | none =>
      simp [profiledRawJointUnitLeftTargetProjection, hslot,
        erasePairedProfiledState, pairedLeftCloseTarget] at hclose
  | some slot =>
      let seed : ProfiledRawJointUnitRightPolicyMacro A strategy
          (childSource.code A) policy := {
        state := policy.run []
        reachable := ⟨[], rfl⟩
        slot := slot
        active_slot := by
          rw [hrootCode, hcode, hslot] }
      exact ⟨⟨childSource, hcode, policy, seed, rfl⟩⟩

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- The simultaneous mirrored member has the same left-close orientation. -/
theorem
    nonempty_profiledRawJointStrictRightPostResolveFiniteLeftCloseFreshPolicyPackage_of_commonTarget
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (target : ProfiledRawJointUnitTarget A)
    (htarget : ProfiledRawJointStrictRightPostResolveFiniteTargetMeaning A
      strategy hwin initial entry input true target)
    (scan : PairedLeftScanState A) (row : PairedEntryRow)
    (physical : PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hclose : erasePairedProfiledState A
        (profiledRawJointUnitLeftTargetProjection A target) =
      pairedLeftCloseTarget A scan row physical) :
    Nonempty
      (ProfiledRawJointLeftCloseFreshPolicyPackage A strategy target) := by
  exact nonempty_profiledRawJointLeftCloseFreshPolicyPackage_of_close A hwin
    (strictRightParent A strategy initial).family
      (strictRightActual entry input).direction target htarget scan row physical
        hclose

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Either mirrored member supplies an explicitly right-oriented recurrent
root. -/
theorem
    nonempty_profiledRawJointStrictRightPostResolveFiniteLeftCloseFreshPolicyPackage_of_targetMeaning
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (branch : Bool) (target : ProfiledRawJointUnitTarget A)
    (htarget : ProfiledRawJointStrictRightPostResolveFiniteTargetMeaning A
      strategy hwin initial entry input branch target)
    (scan : PairedLeftScanState A) (row : PairedEntryRow)
    (physical : PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hclose : erasePairedProfiledState A
        (profiledRawJointUnitLeftTargetProjection A target) =
      pairedLeftCloseTarget A scan row physical) :
    Nonempty
      (ProfiledRawJointLeftCloseFreshPolicyPackage A strategy target) := by
  cases branch with
  | false =>
      exact
        nonempty_profiledRawJointStrictRightPostResolveFiniteLeftCloseFreshPolicyPackage_of_strictTarget
          A strategy hwin initial entry input target htarget scan row physical
            hclose
  | true =>
      exact
        nonempty_profiledRawJointStrictRightPostResolveFiniteLeftCloseFreshPolicyPackage_of_commonTarget
          A strategy hwin initial entry input target htarget scan row physical
            hclose

/-! ## Public occurrence interface for transition-linked enrichments

The bare finite installation above intentionally exposes only incidence-code
targets.  A recurrent construction which must retain a child table has to
decorate the semantic activations *before* narrowing.  The following aliases
export exactly the occurrence-local data needed for that construction while
keeping the implementation abbreviations above private. -/

/-- Common process-one semantic root paired with the literal strict-left
root.  It is the full semantic child from which the two sibling obligations
were obtained. -/
noncomputable def profiledRawJointStrictLeftPostResolveCommonFamily
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    ProfiledRawJointSemanticFamily A strategy (I := Unit) :=
  (strictLeftParent A strategy initial).family.semanticChild A
    (strictLeftActual entry input).direction

/-- The exact root-pinned one-sided semantic source used by the strict
process-one activation.  Its code agrees with the literal strict child, but
the source itself is retained here because its next-table annotation must not
be reconstructed from that code. -/
noncomputable def profiledRawJointStrictLeftPostResolveStrictState
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    ProfiledRawJointOneSidedSemanticState A strategy (I := Unit) :=
  profiledRawJointRootPinnedSelectedSource A strategy
    (StrictLeftChild A strategy initial entry input)
    (StrictLeftPredicate A strategy initial entry input)
    (StrictLeftPolicy A strategy hwin initial entry input)

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Exact target formula of the exported strict process-one activation. -/
theorem profiledRawJointStrictLeftPostResolveStrictActivation_target
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (nextInput : In₂ × In₁) :
    (strictLeftFiniteActivation A strategy hwin initial entry input).target
        row past nextInput =
      profiledRawJointOneSidedNext A
        (profiledRawJointStrictLeftPostResolveStrictState A strategy hwin
          initial entry input).code
        (profiledRawJointStrictLeftPostResolveStrictState A strategy hwin
          initial entry input).move
        (profiledRawJointUnitRightActualDirection row past nextInput) := by
  rfl

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Exact target formula of the paired common process-one activation. -/
theorem profiledRawJointStrictLeftPostResolveCommonActivation_target
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (nextInput : In₂ × In₁) :
    (commonAfterLeftFiniteActivation A strategy hwin initial entry input).target
        row past nextInput =
      profiledRawJointOneSidedNext A
        (profiledRawJointStrictLeftPostResolveCommonFamily A strategy initial
          entry input).incidenceCode
        (profiledRawJointStrictLeftPostResolveCommonFamily A strategy initial
          entry input).move
        (profiledRawJointUnitRightActualDirection row past nextInput) := by
  rfl

noncomputable abbrev profiledRawJointStrictLeftPostResolveSource
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :=
  StrictLeftSource A strategy initial entry input

/-- Exact strict process-one activation, with its literal-child target map
still present. -/
noncomputable abbrev profiledRawJointStrictLeftPostResolveStrictActivation
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :=
  strictLeftFiniteActivation A strategy hwin initial entry input

/-- Simultaneous process-one activation paired with the preceding strict
activation. -/
noncomputable abbrev profiledRawJointStrictLeftPostResolveCommonActivation
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :=
  commonAfterLeftFiniteActivation A strategy hwin initial entry input

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Both exported process-one activations use the literal lambda of the same
pending pair. -/
theorem profiledRawJointStrictLeftPostResolveStrictActivation_lambda
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    (profiledRawJointStrictLeftPostResolveStrictActivation A strategy hwin
      initial entry input).lambda =
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictLeftPairAt
        A strategy initial entry input).1.lambdaOfStrategy :=
  strictLeftActivation_lambda A strategy hwin initial entry input

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
theorem profiledRawJointStrictLeftPostResolveCommonActivation_lambda
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    (profiledRawJointStrictLeftPostResolveCommonActivation A strategy hwin
      initial entry input).lambda =
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictLeftPairAt
        A strategy initial entry input).1.lambdaOfStrategy := by
  rfl

/-- Mirrored full semantic root paired with the literal strict-right root. -/
noncomputable def profiledRawJointStrictRightPostResolveCommonFamily
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    ProfiledRawJointSemanticFamily A strategy (I := Unit) :=
  (strictRightParent A strategy initial).family.semanticChild A
    (strictRightActual entry input).direction

/-- Exact root-pinned one-sided source used by the strict process-two
activation. -/
noncomputable def profiledRawJointStrictRightPostResolveStrictState
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    ProfiledRawJointOneSidedSemanticState A strategy (I := Unit) :=
  profiledRawJointRootPinnedSelectedSource A strategy
    (StrictRightChild A strategy initial entry input)
    (StrictRightPredicate A strategy initial entry input)
    (StrictRightPolicy A strategy hwin initial entry input)

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
theorem profiledRawJointStrictRightPostResolveStrictActivation_target
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (nextInput : In₁ × In₂) :
    (strictRightFiniteActivation A strategy hwin initial entry input).target
        row past nextInput =
      profiledRawJointOneSidedNext A
        (profiledRawJointStrictRightPostResolveStrictState A strategy hwin
          initial entry input).code
        (profiledRawJointStrictRightPostResolveStrictState A strategy hwin
          initial entry input).move
        (profiledRawJointUnitLeftActualDirection row past nextInput) := by
  rfl

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
theorem profiledRawJointStrictRightPostResolveCommonActivation_target
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (nextInput : In₁ × In₂) :
    (commonAfterRightFiniteActivation A strategy hwin initial entry input).target
        row past nextInput =
      profiledRawJointOneSidedNext A
        (profiledRawJointStrictRightPostResolveCommonFamily A strategy initial
          entry input).incidenceCode
        (profiledRawJointStrictRightPostResolveCommonFamily A strategy initial
          entry input).move
        (profiledRawJointUnitLeftActualDirection row past nextInput) := by
  rfl

noncomputable abbrev profiledRawJointStrictRightPostResolveSource
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :=
  StrictRightSource A strategy initial entry input

noncomputable abbrev profiledRawJointStrictRightPostResolveStrictActivation
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :=
  strictRightFiniteActivation A strategy hwin initial entry input

noncomputable abbrev profiledRawJointStrictRightPostResolveCommonActivation
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :=
  commonAfterRightFiniteActivation A strategy hwin initial entry input

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
theorem profiledRawJointStrictRightPostResolveStrictActivation_lambda
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    (profiledRawJointStrictRightPostResolveStrictActivation A strategy hwin
      initial entry input).lambda =
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictRightPairAt
        A strategy initial entry input).1.lambdaOfStrategy :=
  strictRightActivation_lambda A strategy hwin initial entry input

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
theorem profiledRawJointStrictRightPostResolveCommonActivation_lambda
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    (profiledRawJointStrictRightPostResolveCommonActivation A strategy hwin
      initial entry input).lambda =
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictRightPairAt
        A strategy initial entry input).1.lambdaOfStrategy := by
  rfl

end

end DetParityAutomaton

end DistributedSynthesis
