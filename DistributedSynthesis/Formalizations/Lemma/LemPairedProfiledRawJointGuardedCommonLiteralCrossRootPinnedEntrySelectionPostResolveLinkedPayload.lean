/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionPostResolveTransitionKeyAudit
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridFinitePayloadLiteralPrefixMove
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalEdgeAnnotation

/-!
# Occurrence-linked targets for the post-resolve table

The bare post-resolve receiver alphabet is too weak for recurrent use.  Its
target predicate is checked separately at each row, so a narrowed receiver
record need not retain one semantic witness shared by its `first` and `both`
targets.  Recovering that witness after narrowing is therefore not a sound
proof route.

This file performs the required repair before narrowing.  Every semantic
target is enriched with its literal row and with the finite physical-edge
annotation selected from the same current common occurrence and raw
direction.  That annotation already contains the next jointly narrowed
sibling tables.  We then narrow the strict and common activations together.
The resulting move alphabet is globally finite, and its full receiver output
retains the occurrence-linked annotation without storing a history.

The first- and second-record equations below are the fail-fast test for the
construction: both hidden members return exactly the semantic payload, while
the blind sender is one common table.  Arbitrary-prefix target extraction is
the next interface to expose; it follows from the linked descriptor's image
predicate rather than from equality of two bare row targets.
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

private abbrev HybridDirection :=
  ProfiledRawJointHybridDirection (In₁ := In₁) (In₂ := In₂)

private abbrev EdgeAnnotation :=
  ProfiledRawJointHybridPhysicalEdgeAnnotation A

/-- Both current semantic members have their own exact source family.  A
target carries both finite annotations; after the delivered member is known,
the executable handoff selects its corresponding entry. -/
private abbrev Payload := Bool → EdgeAnnotation A

/-! ## The occurrence-linked payload -/

/-- Interpret either hybrid direction as the literal raw-family direction
used to select the next finite sibling tables. -/
private def familyDirectionOfHybrid :
    HybridDirection (In₁ := In₁) (In₂ := In₂) →
      ProfiledRawJointFamilyDirection
        (I := Unit) (In₁ := In₁) (In₂ := In₂)
  | .simultaneous input => profiledRawJointBothRestartDirection input
  | .strict actual => actual.direction

/-- Exact semantic source family of either process-one table member. -/
noncomputable def profiledRawJointStrictLeftPostResolveLinkedSourceFamily
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    Bool → ProfiledRawJointSemanticFamily A strategy (I := Unit)
  | false =>
      (profiledRawJointStrictLeftPostResolveStrictState A strategy hwin
        initial entry input).family
  | true =>
      profiledRawJointStrictLeftPostResolveCommonFamily A strategy initial
        entry input

/-- Exact semantic source family of either process-two table member. -/
noncomputable def profiledRawJointStrictRightPostResolveLinkedSourceFamily
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    Bool → ProfiledRawJointSemanticFamily A strategy (I := Unit)
  | false =>
      (profiledRawJointStrictRightPostResolveStrictState A strategy hwin
        initial entry input).family
  | true =>
      profiledRawJointStrictRightPostResolveCommonFamily A strategy initial
        entry input

/-- The two next-table annotations attached to every process-one target.  The
`false` entry is selected from the exact root-pinned strict source and the
`true` entry from the paired simultaneous source.  Both are chosen before
narrowing. -/
noncomputable def profiledRawJointStrictLeftPostResolveLinkedChildren
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (direction : HybridDirection (In₁ := In₁) (In₂ := In₂)) :
    Payload A :=
  fun member ↦
    profiledRawJointHybridPhysicalAnnotationOf A strategy hwin
      (profiledRawJointStrictLeftPostResolveLinkedSourceFamily A strategy hwin
        initial entry input member)
      (familyDirectionOfHybrid direction)

/-- Mirrored occurrence-linked payload. -/
noncomputable def profiledRawJointStrictRightPostResolveLinkedChildren
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (direction : HybridDirection (In₁ := In₁) (In₂ := In₂)) :
    Payload A :=
  fun member ↦
    profiledRawJointHybridPhysicalAnnotationOf A strategy hwin
      (profiledRawJointStrictRightPostResolveLinkedSourceFamily A strategy hwin
        initial entry input member)
      (familyDirectionOfHybrid direction)

/-- Selecting the current member from the process-one annotation bank gives
the exact live root of that member's one-sided successor. -/
theorem profiledRawJointStrictLeftPostResolveLinkedChildren_strictRoot
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) (row : PairedEntryRow) (past : List (In₂ × In₁))
    (nextInput : In₂ × In₁) :
    let actual := profiledRawJointUnitRightActualDirection
      (In₁ := In₁) (In₂ := In₂) row past nextInput
    let family :=
      profiledRawJointStrictLeftPostResolveLinkedSourceFamily A strategy hwin
        initial entry input member
    profiledRawJointHybridStrictPhysicalCutRoot A actual
        (profiledRawJointStrictLeftPostResolveLinkedChildren A strategy hwin
          initial entry input (.strict actual) member) =
      profiledRawJointOneSidedCurrentSlots A .left
        (profiledRawJointOneSidedNext A (family.incidenceCode A)
          (family.move A) actual) () := by
  dsimp only
  let family :=
    profiledRawJointStrictLeftPostResolveLinkedSourceFamily A strategy hwin
      initial entry input member
  let direction := (profiledRawJointUnitRightActualDirection
    (In₁ := In₁) (In₂ := In₂) row past nextInput).direction
  have hroot :=
    profiledRawJointHybridPhysicalAnnotationOf_rightActual_root_eq A strategy
      hwin family direction
  have hslots :
      ((family.rightActualChild A direction).incidenceCode A).family.left =
        (profiledRawJointRightActualIncidenceNext A
          (family.incidenceCode A).family (family.move A) direction).family.left := by
    simpa [ProfiledRawJointSemanticFamily.incidenceCode,
      ProfiledRawJointSemanticFamily.rightActualChild,
      profiledRawJointRightActualIncidenceNext,
      profiledRawJointRightActualFamilyNext] using
      (family.semanticChild_code_left A direction)
  change Option.map (fun move ↦
      (.inr move.1.source : ProfiledRawJointThreadRoot A))
        (profiledRawJointHybridPhysicalAnnotationOf A strategy hwin family
          direction).2 =
      Option.map Sum.inr
        (((family.rightActualChild A direction).incidenceCode A).family.left
          ()) at hroot
  rw [hslots] at hroot
  simpa [profiledRawJointStrictLeftPostResolveLinkedChildren,
    familyDirectionOfHybrid, profiledRawJointHybridStrictPhysicalCutRoot,
    profiledRawJointOneSidedNext,
    profiledRawJointOneSidedCurrentSlots, family, direction] using hroot

/-- Process-two member-selected annotation/root mirror. -/
theorem profiledRawJointStrictRightPostResolveLinkedChildren_strictRoot
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) (row : PairedEntryRow) (past : List (In₁ × In₂))
    (nextInput : In₁ × In₂) :
    let actual := profiledRawJointUnitLeftActualDirection
      (In₁ := In₁) (In₂ := In₂) row past nextInput
    let family :=
      profiledRawJointStrictRightPostResolveLinkedSourceFamily A strategy hwin
        initial entry input member
    profiledRawJointHybridStrictPhysicalCutRoot A actual
        (profiledRawJointStrictRightPostResolveLinkedChildren A strategy hwin
          initial entry input (.strict actual) member) =
      profiledRawJointOneSidedCurrentSlots A .right
        (profiledRawJointOneSidedNext A (family.incidenceCode A)
          (family.move A) actual) () := by
  dsimp only
  let family :=
    profiledRawJointStrictRightPostResolveLinkedSourceFamily A strategy hwin
      initial entry input member
  let direction := (profiledRawJointUnitLeftActualDirection
    (In₁ := In₁) (In₂ := In₂) row past nextInput).direction
  have hroot :=
    profiledRawJointHybridPhysicalAnnotationOf_leftActual_root_eq A strategy
      hwin family direction
  have hslots :
      ((family.leftActualChild A direction).incidenceCode A).family.right =
        (profiledRawJointLeftActualIncidenceNext A
          (family.incidenceCode A).family (family.move A) direction).family.right := by
    simpa [ProfiledRawJointSemanticFamily.incidenceCode,
      ProfiledRawJointSemanticFamily.leftActualChild,
      profiledRawJointLeftActualIncidenceNext,
      profiledRawJointLeftActualFamilyNext] using
      (family.semanticChild_code_right A direction)
  change Option.map (fun move ↦
      (.inl move.1.source : ProfiledRawJointThreadRoot A))
        (profiledRawJointHybridPhysicalAnnotationOf A strategy hwin family
          direction).1 =
      Option.map Sum.inl
        (((family.leftActualChild A direction).incidenceCode A).family.right
          ()) at hroot
  rw [hslots] at hroot
  simpa [profiledRawJointStrictRightPostResolveLinkedChildren,
    familyDirectionOfHybrid, profiledRawJointHybridStrictPhysicalCutRoot,
    profiledRawJointOneSidedNext,
    profiledRawJointOneSidedCurrentSlots, family, direction] using hroot

/-! ## One common target predicate for the two activations -/

/-- Exact union of the strict and common process-one semantic target images.
The Boolean is proof-side; it is not an executable input. -/
def ProfiledRawJointStrictLeftPostResolveLinkedAllowed
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (target : ProfiledRawJointUnitTarget A) : Prop :=
  ∃ (member : Bool) (row : PairedEntryRow)
      (past : List (In₂ × In₁)) (nextInput : In₂ × In₁),
    target = match member with
      | false =>
          (profiledRawJointStrictLeftPostResolveStrictActivation A strategy
            hwin initial entry input).target row past nextInput
      | true =>
          (profiledRawJointStrictLeftPostResolveCommonActivation A strategy
            hwin initial entry input).target row past nextInput

/-- Reindex both process-one activations to the common image predicate. -/
noncomputable def profiledRawJointStrictLeftPostResolveLinkedActivation
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) :
    ProfiledRawJointTargetRightBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitRightTargetProjection A)
      (ProfiledRawJointStrictLeftPostResolveLinkedAllowed A strategy hwin
        initial entry input)
      (profiledRawJointStrictLeftPostResolveSource A strategy initial entry
        input) := by
  cases member with
  | false =>
      let base :=
        profiledRawJointStrictLeftPostResolveStrictActivation A strategy hwin
          initial entry input
      exact {
        lambda := base.lambda
        initial_profile := base.initial_profile
        forever := base.forever
        target := base.target
        target_allowed := fun row past nextInput ↦
          ⟨false, row, past, nextInput, rfl⟩
        target_state := base.target_state }
  | true =>
      let base :=
        profiledRawJointStrictLeftPostResolveCommonActivation A strategy hwin
          initial entry input
      exact {
        lambda := base.lambda
        initial_profile := base.initial_profile
        forever := base.forever
        target := base.target
        target_allowed := fun row past nextInput ↦
          ⟨true, row, past, nextInput, rfl⟩
        target_state := base.target_state }

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
theorem profiledRawJointStrictLeftPostResolveLinkedActivation_sender_eq
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) :
    pairedRightSenderStrategy
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictLeftPairAt
          A strategy initial entry input).1.lambdaOfStrategy =
      pairedRightSenderStrategy
        (profiledRawJointStrictLeftPostResolveLinkedActivation A strategy hwin
          initial entry input member).lambda := by
  cases member with
  | false =>
      simp only [profiledRawJointStrictLeftPostResolveLinkedActivation]
      rw [profiledRawJointStrictLeftPostResolveStrictActivation_lambda A
        strategy hwin initial entry input]
  | true =>
      simp only [profiledRawJointStrictLeftPostResolveLinkedActivation]
      rw [profiledRawJointStrictLeftPostResolveCommonActivation_lambda A
        strategy hwin initial entry input]

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- The target map of either linked process-one member is the literal
one-sided successor of that member's exact semantic source family. -/
theorem profiledRawJointStrictLeftPostResolveLinkedActivation_target
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) (row : PairedEntryRow) (past : List (In₂ × In₁))
    (nextInput : In₂ × In₁) :
    (profiledRawJointStrictLeftPostResolveLinkedActivation A strategy hwin
        initial entry input member).target row past nextInput =
      profiledRawJointOneSidedNext A
        (profiledRawJointStrictLeftPostResolveLinkedSourceFamily A strategy
          hwin initial entry input member).incidenceCode
        (profiledRawJointStrictLeftPostResolveLinkedSourceFamily A strategy
          hwin initial entry input member).move
        (profiledRawJointUnitRightActualDirection row past nextInput) := by
  cases member with
  | false =>
      simpa [profiledRawJointStrictLeftPostResolveLinkedActivation,
        profiledRawJointStrictLeftPostResolveLinkedSourceFamily,
        ProfiledRawJointOneSidedSemanticState.code,
        ProfiledRawJointOneSidedSemanticState.move] using
        (profiledRawJointStrictLeftPostResolveStrictActivation_target A
          strategy hwin initial entry input row past nextInput)
  | true =>
      simpa [profiledRawJointStrictLeftPostResolveLinkedActivation,
        profiledRawJointStrictLeftPostResolveLinkedSourceFamily] using
        (profiledRawJointStrictLeftPostResolveCommonActivation_target A
          strategy hwin initial entry input row past nextInput)

/-- The member-selected process-one annotation is rooted at the live slot of
the very target emitted by that member's linked activation.  This is the
local compatibility equation needed by the executable handoff. -/
theorem profiledRawJointStrictLeftPostResolveLinkedChildren_targetRoot
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) (row : PairedEntryRow) (past : List (In₂ × In₁))
    (nextInput : In₂ × In₁) :
    let actual := profiledRawJointUnitRightActualDirection
      (In₁ := In₁) (In₂ := In₂) row past nextInput
    profiledRawJointHybridStrictPhysicalCutRoot A actual
        (profiledRawJointStrictLeftPostResolveLinkedChildren A strategy hwin
          initial entry input (.strict actual) member) =
      profiledRawJointOneSidedCurrentSlots A .left
        ((profiledRawJointStrictLeftPostResolveLinkedActivation A strategy
          hwin initial entry input member).target row past nextInput) () := by
  dsimp only
  rw [profiledRawJointStrictLeftPostResolveLinkedActivation_target A strategy
    hwin initial entry input member row past nextInput]
  exact
    profiledRawJointStrictLeftPostResolveLinkedChildren_strictRoot A strategy
      hwin initial entry input member row past nextInput

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Every process-one linked target has a live process-two slot. -/
theorem profiledRawJointStrictLeftPostResolveLinkedActivation_target_live
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) (row : PairedEntryRow) (past : List (In₂ × In₁))
    (nextInput : In₂ × In₁) :
    ∃ slot : ProfiledRawLeftSlot A,
      profiledRawJointOneSidedCurrentSlots A .left
          ((profiledRawJointStrictLeftPostResolveLinkedActivation A strategy
            hwin initial entry input member).target row past nextInput) () =
        some (.inr slot) := by
  let activation :=
    profiledRawJointStrictLeftPostResolveLinkedActivation A strategy hwin
      initial entry input member
  have hstate := activation.target_state row past nextInput
  cases hslot : (activation.target row past nextInput).family.left () with
  | none =>
      simp [profiledRawJointUnitRightTargetProjection, hslot] at hstate
  | some slot =>
      refine ⟨slot, ?_⟩
      change Option.map Sum.inr
          ((activation.target row past nextInput).family.left ()) = _
      simp [hslot]

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- More than liveness is retained at a process-one target: its unique live
process-two slot is the finite erasure of the literal fresh paired entry
generated from the same post-resolve pair, row, prefix, and closing input.
In particular the new pair carries a genuine `ProcTwoPendingOverlap`; it is
not reconstructed from the emitted incidence code. -/
theorem profiledRawJointStrictLeftPostResolveLinkedActivation_target_pair
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) (row : PairedEntryRow) (past : List (In₂ × In₁))
    (nextInput : In₂ × In₁) :
    let parent :=
      profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictLeftPairAt
        A strategy initial entry input
    let child := profiledRawRightSemanticChildPair A parent row past nextInput
    ProcTwoPendingOverlap child.1.rightHistory child.1.bothHistory ∧
      ((profiledRawJointStrictLeftPostResolveLinkedActivation A strategy hwin
        initial entry input member).target row past nextInput).family.left () =
        some (profiledRawLeftSlotOfSemanticPair A child) := by
  dsimp only
  let activation :=
    profiledRawJointStrictLeftPostResolveLinkedActivation A strategy hwin
      initial entry input member
  let parent :=
    profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictLeftPairAt
      A strategy initial entry input
  let child := profiledRawRightSemanticChildPair A parent row past nextInput
  refine ⟨child.1.pending, ?_⟩
  have hstate := activation.target_state row past nextInput
  have hlambda : activation.lambda = parent.1.lambdaOfStrategy := by
    cases member with
    | false =>
        simpa [activation, parent,
          profiledRawJointStrictLeftPostResolveLinkedActivation] using
          (profiledRawJointStrictLeftPostResolveStrictActivation_lambda A
            strategy hwin initial entry input)
    | true =>
        simpa [activation, parent,
          profiledRawJointStrictLeftPostResolveLinkedActivation] using
          (profiledRawJointStrictLeftPostResolveCommonActivation_lambda A
            strategy hwin initial entry input)
  have hchildSlot :
      profiledRawRightChildSlot A
          (profiledRawJointStrictLeftPostResolveSource A strategy initial entry
            input)
          activation.lambda row past nextInput =
        profiledRawLeftSlotOfSemanticPair A child := by
    rw [hlambda]
    simpa [parent, child,
      profiledRawJointStrictLeftPostResolveSource] using
      (profiledRawRightChildSlot_eq_semanticChildPairCode
        (I := Unit) A
        (profiledRawJointUnitRightActualDirection
          (In₁ := In₁) (In₂ := In₂) row past nextInput).direction
        parent row)
  rw [hchildSlot] at hstate
  cases htarget : (activation.target row past nextInput).family.left () with
  | none =>
      simp [profiledRawJointUnitRightTargetProjection, htarget] at hstate
  | some slot =>
      simpa [profiledRawJointUnitRightTargetProjection, htarget] using hstate

/-- Consequently the selected annotation bank really contains the next
process-two table, and that table is rooted at the emitted target. -/
theorem profiledRawJointStrictLeftPostResolveLinkedChildren_move_exists
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) (row : PairedEntryRow) (past : List (In₂ × In₁))
    (nextInput : In₂ × In₁) :
    ∃ move : ProfiledRawJointLeftPhysicalSiblingMove A,
      (profiledRawJointStrictLeftPostResolveLinkedChildren A strategy hwin
          initial entry input
          (.strict (profiledRawJointUnitRightActualDirection row past
            nextInput)) member).2 = some move ∧
      profiledRawJointOneSidedCurrentSlots A .left
          ((profiledRawJointStrictLeftPostResolveLinkedActivation A strategy
            hwin initial entry input member).target row past nextInput) () =
        some (.inr move.1.source) := by
  obtain ⟨slot, hlive⟩ :=
    profiledRawJointStrictLeftPostResolveLinkedActivation_target_live A
      strategy hwin initial entry input member row past nextInput
  have hroot :=
    profiledRawJointStrictLeftPostResolveLinkedChildren_targetRoot A strategy
      hwin initial entry input member row past nextInput
  change Option.map (fun move ↦
      (.inr move.1.source : ProfiledRawJointThreadRoot A))
      (profiledRawJointStrictLeftPostResolveLinkedChildren A strategy hwin
        initial entry input
        (.strict (profiledRawJointUnitRightActualDirection row past
          nextInput)) member).2 = _ at hroot
  rw [hlive] at hroot
  cases hmove :
      (profiledRawJointStrictLeftPostResolveLinkedChildren A strategy hwin
        initial entry input
        (.strict (profiledRawJointUnitRightActualDirection row past
          nextInput)) member).2 with
  | none => simp [hmove] at hroot
  | some move =>
      have hsource : move.1.source = slot := by
        simpa [hmove] using hroot
      refine ⟨move, rfl, ?_⟩
      rw [hlive, hsource]

/-- Exact union for the process-two mirror. -/
def ProfiledRawJointStrictRightPostResolveLinkedAllowed
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (target : ProfiledRawJointUnitTarget A) : Prop :=
  ∃ (member : Bool) (row : PairedEntryRow)
      (past : List (In₁ × In₂)) (nextInput : In₁ × In₂),
    target = match member with
      | false =>
          (profiledRawJointStrictRightPostResolveStrictActivation A strategy
            hwin initial entry input).target row past nextInput
      | true =>
          (profiledRawJointStrictRightPostResolveCommonActivation A strategy
            hwin initial entry input).target row past nextInput

noncomputable def profiledRawJointStrictRightPostResolveLinkedActivation
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) :
    ProfiledRawJointTargetLeftBlockActivation A
      (ProfiledRawJointUnitTarget A)
      (profiledRawJointUnitLeftTargetProjection A)
      (ProfiledRawJointStrictRightPostResolveLinkedAllowed A strategy hwin
        initial entry input)
      (profiledRawJointStrictRightPostResolveSource A strategy initial entry
        input) := by
  cases member with
  | false =>
      let base :=
        profiledRawJointStrictRightPostResolveStrictActivation A strategy hwin
          initial entry input
      exact {
        lambda := base.lambda
        initial_profile := base.initial_profile
        forever := base.forever
        target := base.target
        target_allowed := fun row past nextInput ↦
          ⟨false, row, past, nextInput, rfl⟩
        target_state := base.target_state }
  | true =>
      let base :=
        profiledRawJointStrictRightPostResolveCommonActivation A strategy hwin
          initial entry input
      exact {
        lambda := base.lambda
        initial_profile := base.initial_profile
        forever := base.forever
        target := base.target
        target_allowed := fun row past nextInput ↦
          ⟨true, row, past, nextInput, rfl⟩
        target_state := base.target_state }

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
theorem profiledRawJointStrictRightPostResolveLinkedActivation_sender_eq
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) :
    pairedLeftSenderStrategy
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictRightPairAt
          A strategy initial entry input).1.lambdaOfStrategy =
      pairedLeftSenderStrategy
        (profiledRawJointStrictRightPostResolveLinkedActivation A strategy
          hwin initial entry input member).lambda := by
  cases member with
  | false =>
      simp only [profiledRawJointStrictRightPostResolveLinkedActivation]
      rw [profiledRawJointStrictRightPostResolveStrictActivation_lambda A
        strategy hwin initial entry input]
  | true =>
      simp only [profiledRawJointStrictRightPostResolveLinkedActivation]
      rw [profiledRawJointStrictRightPostResolveCommonActivation_lambda A
        strategy hwin initial entry input]

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Process-two target-source mirror. -/
theorem profiledRawJointStrictRightPostResolveLinkedActivation_target
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) (row : PairedEntryRow) (past : List (In₁ × In₂))
    (nextInput : In₁ × In₂) :
    (profiledRawJointStrictRightPostResolveLinkedActivation A strategy hwin
        initial entry input member).target row past nextInput =
      profiledRawJointOneSidedNext A
        (profiledRawJointStrictRightPostResolveLinkedSourceFamily A strategy
          hwin initial entry input member).incidenceCode
        (profiledRawJointStrictRightPostResolveLinkedSourceFamily A strategy
          hwin initial entry input member).move
        (profiledRawJointUnitLeftActualDirection row past nextInput) := by
  cases member with
  | false =>
      simpa [profiledRawJointStrictRightPostResolveLinkedActivation,
        profiledRawJointStrictRightPostResolveLinkedSourceFamily,
        ProfiledRawJointOneSidedSemanticState.code,
        ProfiledRawJointOneSidedSemanticState.move] using
        (profiledRawJointStrictRightPostResolveStrictActivation_target A
          strategy hwin initial entry input row past nextInput)
  | true =>
      simpa [profiledRawJointStrictRightPostResolveLinkedActivation,
        profiledRawJointStrictRightPostResolveLinkedSourceFamily] using
        (profiledRawJointStrictRightPostResolveCommonActivation_target A
          strategy hwin initial entry input row past nextInput)

/-- Process-two target/root compatibility mirror. -/
theorem profiledRawJointStrictRightPostResolveLinkedChildren_targetRoot
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) (row : PairedEntryRow) (past : List (In₁ × In₂))
    (nextInput : In₁ × In₂) :
    let actual := profiledRawJointUnitLeftActualDirection
      (In₁ := In₁) (In₂ := In₂) row past nextInput
    profiledRawJointHybridStrictPhysicalCutRoot A actual
        (profiledRawJointStrictRightPostResolveLinkedChildren A strategy hwin
          initial entry input (.strict actual) member) =
      profiledRawJointOneSidedCurrentSlots A .right
        ((profiledRawJointStrictRightPostResolveLinkedActivation A strategy
          hwin initial entry input member).target row past nextInput) () := by
  dsimp only
  rw [profiledRawJointStrictRightPostResolveLinkedActivation_target A strategy
    hwin initial entry input member row past nextInput]
  exact
    profiledRawJointStrictRightPostResolveLinkedChildren_strictRoot A strategy
      hwin initial entry input member row past nextInput

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Every process-two linked target has a live process-one slot. -/
theorem profiledRawJointStrictRightPostResolveLinkedActivation_target_live
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) (row : PairedEntryRow) (past : List (In₁ × In₂))
    (nextInput : In₁ × In₂) :
    ∃ slot : ProfiledRawRightSlot A,
      profiledRawJointOneSidedCurrentSlots A .right
          ((profiledRawJointStrictRightPostResolveLinkedActivation A strategy
            hwin initial entry input member).target row past nextInput) () =
        some (.inl slot) := by
  let activation :=
    profiledRawJointStrictRightPostResolveLinkedActivation A strategy hwin
      initial entry input member
  have hstate := activation.target_state row past nextInput
  cases hslot : (activation.target row past nextInput).family.right () with
  | none =>
      simp [profiledRawJointUnitLeftTargetProjection, hslot] at hstate
  | some slot =>
      refine ⟨slot, ?_⟩
      change Option.map Sum.inl
          ((activation.target row past nextInput).family.right ()) = _
      simp [hslot]

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Mirrored exact fresh-pair statement.  The target's live process-one slot
is the erasure of a literal paired entry with its intrinsic
`ProcOnePendingOverlap` proof. -/
theorem profiledRawJointStrictRightPostResolveLinkedActivation_target_pair
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) (row : PairedEntryRow) (past : List (In₁ × In₂))
    (nextInput : In₁ × In₂) :
    let parent :=
      profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictRightPairAt
        A strategy initial entry input
    let child := profiledRawLeftSemanticChildPair A parent row past nextInput
    ProcOnePendingOverlap child.1.leftHistory child.1.bothHistory ∧
      ((profiledRawJointStrictRightPostResolveLinkedActivation A strategy hwin
        initial entry input member).target row past nextInput).family.right () =
        some (profiledRawRightSlotOfSemanticPair A child) := by
  dsimp only
  let activation :=
    profiledRawJointStrictRightPostResolveLinkedActivation A strategy hwin
      initial entry input member
  let parent :=
    profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictRightPairAt
      A strategy initial entry input
  let child := profiledRawLeftSemanticChildPair A parent row past nextInput
  refine ⟨child.1.pending, ?_⟩
  have hstate := activation.target_state row past nextInput
  have hlambda : activation.lambda = parent.1.lambdaOfStrategy := by
    cases member with
    | false =>
        simpa [activation, parent,
          profiledRawJointStrictRightPostResolveLinkedActivation] using
          (profiledRawJointStrictRightPostResolveStrictActivation_lambda A
            strategy hwin initial entry input)
    | true =>
        simpa [activation, parent,
          profiledRawJointStrictRightPostResolveLinkedActivation] using
          (profiledRawJointStrictRightPostResolveCommonActivation_lambda A
            strategy hwin initial entry input)
  have hchildSlot :
      profiledRawLeftChildSlot A
          (profiledRawJointStrictRightPostResolveSource A strategy initial entry
            input)
          activation.lambda row past nextInput =
        profiledRawRightSlotOfSemanticPair A child := by
    rw [hlambda]
    simpa [parent, child,
      profiledRawJointStrictRightPostResolveSource] using
      (profiledRawLeftChildSlot_eq_semanticChildPairCode
        (I := Unit) A
        (profiledRawJointUnitLeftActualDirection
          (In₁ := In₁) (In₂ := In₂) row past nextInput).direction
        parent row)
  rw [hchildSlot] at hstate
  cases htarget : (activation.target row past nextInput).family.right () with
  | none =>
      simp [profiledRawJointUnitLeftTargetProjection, htarget] at hstate
  | some slot =>
      simpa [profiledRawJointUnitLeftTargetProjection, htarget] using hstate

/-- Process-two installed-table mirror. -/
theorem profiledRawJointStrictRightPostResolveLinkedChildren_move_exists
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) (row : PairedEntryRow) (past : List (In₁ × In₂))
    (nextInput : In₁ × In₂) :
    ∃ move : ProfiledRawJointRightPhysicalSiblingMove A,
      (profiledRawJointStrictRightPostResolveLinkedChildren A strategy hwin
          initial entry input
          (.strict (profiledRawJointUnitLeftActualDirection row past
            nextInput)) member).1 = some move ∧
      profiledRawJointOneSidedCurrentSlots A .right
          ((profiledRawJointStrictRightPostResolveLinkedActivation A strategy
            hwin initial entry input member).target row past nextInput) () =
        some (.inl move.1.source) := by
  obtain ⟨slot, hlive⟩ :=
    profiledRawJointStrictRightPostResolveLinkedActivation_target_live A
      strategy hwin initial entry input member row past nextInput
  have hroot :=
    profiledRawJointStrictRightPostResolveLinkedChildren_targetRoot A strategy
      hwin initial entry input member row past nextInput
  change Option.map (fun move ↦
      (.inl move.1.source : ProfiledRawJointThreadRoot A))
      (profiledRawJointStrictRightPostResolveLinkedChildren A strategy hwin
        initial entry input
        (.strict (profiledRawJointUnitLeftActualDirection row past
          nextInput)) member).1 = _ at hroot
  rw [hlive] at hroot
  cases hmove :
      (profiledRawJointStrictRightPostResolveLinkedChildren A strategy hwin
        initial entry input
        (.strict (profiledRawJointUnitLeftActualDirection row past
          nextInput)) member).1 with
  | none => simp [hmove] at hroot
  | some move =>
      have hsource : move.1.source = slot := by
        simpa [hmove] using hroot
      refine ⟨move, rfl, ?_⟩
      rw [hlive, hsource]

/-! ## Globally finite linked moves -/

noncomputable abbrev ProfiledRawJointStrictLeftPostResolveLinkedMove :=
  ProfiledRawJointRightFinitePayloadLiteralPrefixMove A (Payload A)

noncomputable abbrev ProfiledRawJointStrictRightPostResolveLinkedMove :=
  ProfiledRawJointLeftFinitePayloadLiteralPrefixMove A (Payload A)

noncomputable instance :
    Fintype (ProfiledRawJointStrictLeftPostResolveLinkedMove A) := by
  infer_instance

noncomputable instance :
    Fintype (ProfiledRawJointStrictRightPostResolveLinkedMove A) := by
  infer_instance

/-- Simultaneously narrow the payload-enriched strict/common process-one
receivers. -/
noncomputable def profiledRawJointStrictLeftPostResolveLinkedMove
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    ProfiledRawJointStrictLeftPostResolveLinkedMove A :=
  profiledRawJointRightFinitePayloadLiteralPrefixMoveOf A
    (profiledRawJointStrictLeftPostResolveLinkedActivation A strategy hwin
      initial entry input)
    (profiledRawJointStrictLeftPostResolveLinkedChildren A strategy hwin
      initial entry input)
    (pairedRightSenderStrategy
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictLeftPairAt
        A strategy initial entry input).1.lambdaOfStrategy)
    (profiledRawJointStrictLeftPostResolveLinkedActivation_sender_eq A
      strategy hwin initial entry input)

/-- Process-two mirror. -/
noncomputable def profiledRawJointStrictRightPostResolveLinkedMove
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    ProfiledRawJointStrictRightPostResolveLinkedMove A :=
  profiledRawJointLeftFinitePayloadLiteralPrefixMoveOf A
    (profiledRawJointStrictRightPostResolveLinkedActivation A strategy hwin
      initial entry input)
    (profiledRawJointStrictRightPostResolveLinkedChildren A strategy hwin
      initial entry input)
    (pairedLeftSenderStrategy
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictRightPairAt
        A strategy initial entry input).1.lambdaOfStrategy)
    (profiledRawJointStrictRightPostResolveLinkedActivation_sender_eq A
      strategy hwin initial entry input)

/-! ## The payload survives narrowing at the transition frontier -/

/-- At the first process-one receiver record, every queried row returns the
finite annotation selected from the same common occurrence and literal raw
direction.  The statement holds for either hidden strict/common member. -/
theorem profiledRawJointStrictLeftPostResolveLinkedMove_initial_payload
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) (first : In₂ × In₁) (row : PairedEntryRow) :
    let move := profiledRawJointStrictLeftPostResolveLinkedMove A strategy
      hwin initial entry input
    let receiverRoot :=
      profiledRawJointRightFinitePayloadLiteralPrefixReceiverInitial A move
        member
    let output :=
      (profiledRawJointRightFinitePayloadLiteralPrefixReceiverRecv A
        receiverRoot first.1 first.2).1
    profiledRawJointHybridFinitePayloadLinkedTargetPayload A
        (output.target row).1 =
      profiledRawJointStrictLeftPostResolveLinkedChildren A strategy hwin
        initial entry input
        (.strict (profiledRawJointUnitRightActualDirection row [] first)) := by
  exact
    profiledRawJointRightFinitePayloadLiteralPrefixMoveOf_initial_first_payload
      A
      (profiledRawJointStrictLeftPostResolveLinkedActivation A strategy hwin
        initial entry input)
      (profiledRawJointStrictLeftPostResolveLinkedChildren A strategy hwin
        initial entry input)
      (pairedRightSenderStrategy
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictLeftPairAt
          A strategy initial entry input).1.lambdaOfStrategy)
      (profiledRawJointStrictLeftPostResolveLinkedActivation_sender_eq A
        strategy hwin initial entry input)
      member first row

/-- The second retained record has the same occurrence-linked guarantee and
uses the exact one-record past. -/
theorem profiledRawJointStrictLeftPostResolveLinkedMove_second_payload
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) (first second : In₂ × In₁)
    (row : PairedEntryRow) :
    let move := profiledRawJointStrictLeftPostResolveLinkedMove A strategy
      hwin initial entry input
    let receiverRoot :=
      profiledRawJointRightFinitePayloadLiteralPrefixReceiverInitial A move
        member
    let receiverAfterFirst :=
      (profiledRawJointRightFinitePayloadLiteralPrefixReceiverRecv A
        receiverRoot first.1 first.2).2
    let output :=
      (profiledRawJointRightFinitePayloadLiteralPrefixReceiverRecv A
        receiverAfterFirst second.1 second.2).1
    profiledRawJointHybridFinitePayloadLinkedTargetPayload A
        (output.target row).1 =
      profiledRawJointStrictLeftPostResolveLinkedChildren A strategy hwin
        initial entry input
        (.strict (profiledRawJointUnitRightActualDirection row [first]
          second)) := by
  exact
    profiledRawJointRightFinitePayloadLiteralPrefixMoveOf_retained_second_payload
      A
      (profiledRawJointStrictLeftPostResolveLinkedActivation A strategy hwin
        initial entry input)
      (profiledRawJointStrictLeftPostResolveLinkedChildren A strategy hwin
        initial entry input)
      (pairedRightSenderStrategy
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictLeftPairAt
          A strategy initial entry input).1.lambdaOfStrategy)
      (profiledRawJointStrictLeftPostResolveLinkedActivation_sender_eq A
        strategy hwin initial entry input)
      member first second row

theorem profiledRawJointStrictRightPostResolveLinkedMove_initial_payload
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) (first : In₁ × In₂) (row : PairedEntryRow) :
    let move := profiledRawJointStrictRightPostResolveLinkedMove A strategy
      hwin initial entry input
    let receiverRoot :=
      profiledRawJointLeftFinitePayloadLiteralPrefixReceiverInitial A move
        member
    let output :=
      (profiledRawJointLeftFinitePayloadLiteralPrefixReceiverRecv A
        receiverRoot first.1 first.2).1
    profiledRawJointHybridFinitePayloadLinkedTargetPayload A
        (output.target row).1 =
      profiledRawJointStrictRightPostResolveLinkedChildren A strategy hwin
        initial entry input
        (.strict (profiledRawJointUnitLeftActualDirection row [] first)) := by
  exact
    profiledRawJointLeftFinitePayloadLiteralPrefixMoveOf_initial_first_payload A
      (profiledRawJointStrictRightPostResolveLinkedActivation A strategy hwin
        initial entry input)
      (profiledRawJointStrictRightPostResolveLinkedChildren A strategy hwin
        initial entry input)
      (pairedLeftSenderStrategy
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictRightPairAt
          A strategy initial entry input).1.lambdaOfStrategy)
      (profiledRawJointStrictRightPostResolveLinkedActivation_sender_eq A
        strategy hwin initial entry input)
      member first row

theorem profiledRawJointStrictRightPostResolveLinkedMove_second_payload
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) (first second : In₁ × In₂)
    (row : PairedEntryRow) :
    let move := profiledRawJointStrictRightPostResolveLinkedMove A strategy
      hwin initial entry input
    let receiverRoot :=
      profiledRawJointLeftFinitePayloadLiteralPrefixReceiverInitial A move
        member
    let receiverAfterFirst :=
      (profiledRawJointLeftFinitePayloadLiteralPrefixReceiverRecv A
        receiverRoot first.1 first.2).2
    let output :=
      (profiledRawJointLeftFinitePayloadLiteralPrefixReceiverRecv A
        receiverAfterFirst second.1 second.2).1
    profiledRawJointHybridFinitePayloadLinkedTargetPayload A
        (output.target row).1 =
      profiledRawJointStrictRightPostResolveLinkedChildren A strategy hwin
        initial entry input
        (.strict (profiledRawJointUnitLeftActualDirection row [first]
          second)) := by
  exact
    profiledRawJointLeftFinitePayloadLiteralPrefixMoveOf_retained_second_payload
      A
      (profiledRawJointStrictRightPostResolveLinkedActivation A strategy hwin
        initial entry input)
      (profiledRawJointStrictRightPostResolveLinkedChildren A strategy hwin
        initial entry input)
      (pairedLeftSenderStrategy
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictRightPairAt
          A strategy initial entry input).1.lambdaOfStrategy)
      (profiledRawJointStrictRightPostResolveLinkedActivation_sender_eq A
        strategy hwin initial entry input)
      member first second row

/-! ## Arbitrary-prefix occurrence retention

The following interface is the recurrence-critical statement.  It concerns
the complete play generated by the narrowed finite table, not merely the two
records pinned in its descriptor. -/

/-- Complete process-one post-resolve linked play. -/
noncomputable def profiledRawJointStrictLeftPostResolveLinkedMovePlay
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) (env : Nat → In₂ × In₁) :
    Nat → RealizedBlockRound In₂ In₁
      (ProfiledRawJointHybridFinitePayloadRowExactRightReceiverOutput A
        (Bool → ProfiledRawJointHybridPhysicalEdgeAnnotation A)) Out₁ :=
  profiledRawJointRightFinitePayloadLiteralPrefixMoveOfPlay A
    (profiledRawJointStrictLeftPostResolveLinkedActivation A strategy hwin
      initial entry input)
    (profiledRawJointStrictLeftPostResolveLinkedChildren A strategy hwin
      initial entry input)
    (pairedRightSenderStrategy
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictLeftPairAt
        A strategy initial entry input).1.lambdaOfStrategy)
    (profiledRawJointStrictLeftPostResolveLinkedActivation_sender_eq A
      strategy hwin initial entry input)
    member env

/-- Every process-one target at every finite depth is an exact target of the
selected strict/common semantic activation and carries the annotation chosen
from the same current common occurrence and actual raw direction. -/
theorem profiledRawJointStrictLeftPostResolveLinkedMovePlay_target_exists
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) (env : Nat → In₂ × In₁) (n : Nat)
    (row : PairedEntryRow) :
    let play := profiledRawJointStrictLeftPostResolveLinkedMovePlay A strategy
      hwin initial entry input member env
    let projected := BlockRecordMonitor.projectReceiverPlay
      (profiledRawJointHybridFinitePayloadRowExactRightReceiverProjection A)
      play
    ∃ past nextInput,
      (projected n).2.1.target row =
        ((profiledRawJointStrictLeftPostResolveLinkedActivation A strategy
            hwin initial entry input member).target row past nextInput,
          (row,
            profiledRawJointStrictLeftPostResolveLinkedChildren A strategy
              hwin initial entry input
              (.strict (profiledRawJointUnitRightActualDirection row past
                nextInput)))) := by
  exact
    profiledRawJointRightFinitePayloadLiteralPrefixMoveOfPlay_target_exists A
      (profiledRawJointStrictLeftPostResolveLinkedActivation A strategy hwin
        initial entry input)
      (profiledRawJointStrictLeftPostResolveLinkedChildren A strategy hwin
        initial entry input)
      (pairedRightSenderStrategy
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictLeftPairAt
          A strategy initial entry input).1.lambdaOfStrategy)
      (profiledRawJointStrictLeftPostResolveLinkedActivation_sender_eq A
        strategy hwin initial entry input)
      member env n row

/-- Payload-only process-one corollary, convenient for installing the next
finite sibling table. -/
theorem profiledRawJointStrictLeftPostResolveLinkedMovePlay_payload_exists
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) (env : Nat → In₂ × In₁) (n : Nat)
    (row : PairedEntryRow) :
    let play := profiledRawJointStrictLeftPostResolveLinkedMovePlay A strategy
      hwin initial entry input member env
    let projected := BlockRecordMonitor.projectReceiverPlay
      (profiledRawJointHybridFinitePayloadRowExactRightReceiverProjection A)
      play
    ∃ past nextInput,
      profiledRawJointHybridFinitePayloadLinkedTargetPayload A
          ((projected n).2.1.target row) =
        profiledRawJointStrictLeftPostResolveLinkedChildren A strategy hwin
          initial entry input
          (.strict (profiledRawJointUnitRightActualDirection row past
            nextInput)) := by
  dsimp only
  obtain ⟨past, nextInput, htarget⟩ :=
    profiledRawJointStrictLeftPostResolveLinkedMovePlay_target_exists A
      strategy hwin initial entry input member env n row
  refine ⟨past, nextInput, ?_⟩
  rw [htarget]
  rfl

/-- At every depth and row of the executable process-one play, selecting the
delivered member from the carried finite annotation bank yields exactly the
live root of the emitted bare target.  Thus target and next-table data cannot
come from different semantic occurrences. -/
theorem profiledRawJointStrictLeftPostResolveLinkedMovePlay_cutRoot_exists
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) (env : Nat → In₂ × In₁) (n : Nat)
    (row : PairedEntryRow) :
    let play := profiledRawJointStrictLeftPostResolveLinkedMovePlay A strategy
      hwin initial entry input member env
    let projected := BlockRecordMonitor.projectReceiverPlay
      (profiledRawJointHybridFinitePayloadRowExactRightReceiverProjection A)
      play
    ∃ past nextInput,
      let actual := profiledRawJointUnitRightActualDirection
        (In₁ := In₁) (In₂ := In₂) row past nextInput
      profiledRawJointHybridStrictPhysicalCutRoot A actual
          ((profiledRawJointHybridFinitePayloadLinkedTargetPayload A
            ((projected n).2.1.target row)) member) =
        profiledRawJointOneSidedCurrentSlots A .left
          ((projected n).2.1.target row).1 () := by
  dsimp only
  obtain ⟨past, nextInput, htarget⟩ :=
    profiledRawJointStrictLeftPostResolveLinkedMovePlay_target_exists A
      strategy hwin initial entry input member env n row
  refine ⟨past, nextInput, ?_⟩
  rw [htarget]
  simpa using
    (profiledRawJointStrictLeftPostResolveLinkedChildren_targetRoot A strategy
      hwin initial entry input member row past nextInput)

/-- Executable form of the process-one handoff: every emitted row target
carries an actual finite process-two sibling move for the delivered member,
and the move descriptor starts at the target's live root. -/
theorem profiledRawJointStrictLeftPostResolveLinkedMovePlay_installedMove_exists
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) (env : Nat → In₂ × In₁) (n : Nat)
    (row : PairedEntryRow) :
    let play := profiledRawJointStrictLeftPostResolveLinkedMovePlay A strategy
      hwin initial entry input member env
    let projected := BlockRecordMonitor.projectReceiverPlay
      (profiledRawJointHybridFinitePayloadRowExactRightReceiverProjection A)
      play
    ∃ (past : List (In₂ × In₁)) (nextInput : In₂ × In₁)
        (move : ProfiledRawJointLeftPhysicalSiblingMove A),
      (profiledRawJointHybridFinitePayloadLinkedTargetPayload A
          ((projected n).2.1.target row) member).2 = some move ∧
      profiledRawJointOneSidedCurrentSlots A .left
          ((projected n).2.1.target row).1 () =
        some (.inr move.1.source) := by
  dsimp only
  obtain ⟨past, nextInput, htarget⟩ :=
    profiledRawJointStrictLeftPostResolveLinkedMovePlay_target_exists A
      strategy hwin initial entry input member env n row
  obtain ⟨move, hmove, hroot⟩ :=
    profiledRawJointStrictLeftPostResolveLinkedChildren_move_exists A strategy
      hwin initial entry input member row past nextInput
  refine ⟨past, nextInput, move, ?_, ?_⟩
  · rw [htarget]
    exact hmove
  · rw [htarget]
    exact hroot

/-- Arbitrary-depth semantic regeneration for the process-one table.  Each
emitted row target contains the erasure of one literal fresh process-two
paired entry, and that entry itself supplies the next pending-overlap
invariant.  This is stronger than target representability by a code-equal
one-sided state. -/
theorem profiledRawJointStrictLeftPostResolveLinkedMovePlay_targetPair_exists
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) (env : Nat → In₂ × In₁) (n : Nat)
    (row : PairedEntryRow) :
    let play := profiledRawJointStrictLeftPostResolveLinkedMovePlay A strategy
      hwin initial entry input member env
    let projected := BlockRecordMonitor.projectReceiverPlay
      (profiledRawJointHybridFinitePayloadRowExactRightReceiverProjection A)
      play
    ∃ (past : List (In₂ × In₁)) (nextInput : In₂ × In₁),
      let parent :=
        profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictLeftPairAt
          A strategy initial entry input
      let child :=
        profiledRawRightSemanticChildPair A parent row past nextInput
      ProcTwoPendingOverlap child.1.rightHistory child.1.bothHistory ∧
        ((projected n).2.1.target row).1.family.left () =
          some (profiledRawLeftSlotOfSemanticPair A child) := by
  dsimp only
  obtain ⟨past, nextInput, htarget⟩ :=
    profiledRawJointStrictLeftPostResolveLinkedMovePlay_target_exists A
      strategy hwin initial entry input member env n row
  refine ⟨past, nextInput, ?_⟩
  have hpair :=
    profiledRawJointStrictLeftPostResolveLinkedActivation_target_pair A
      strategy hwin initial entry input member row past nextInput
  rw [htarget]
  exact hpair

/-- Complete process-two post-resolve linked play. -/
noncomputable def profiledRawJointStrictRightPostResolveLinkedMovePlay
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) (env : Nat → In₁ × In₂) :
    Nat → RealizedBlockRound In₁ In₂
      (ProfiledRawJointHybridFinitePayloadRowExactLeftReceiverOutput A
        (Bool → ProfiledRawJointHybridPhysicalEdgeAnnotation A)) Out₂ :=
  profiledRawJointLeftFinitePayloadLiteralPrefixMoveOfPlay A
    (profiledRawJointStrictRightPostResolveLinkedActivation A strategy hwin
      initial entry input)
    (profiledRawJointStrictRightPostResolveLinkedChildren A strategy hwin
      initial entry input)
    (pairedLeftSenderStrategy
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictRightPairAt
        A strategy initial entry input).1.lambdaOfStrategy)
    (profiledRawJointStrictRightPostResolveLinkedActivation_sender_eq A
      strategy hwin initial entry input)
    member env

/-- Process-two arbitrary-prefix exact target and annotation readback. -/
theorem profiledRawJointStrictRightPostResolveLinkedMovePlay_target_exists
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) (env : Nat → In₁ × In₂) (n : Nat)
    (row : PairedEntryRow) :
    let play := profiledRawJointStrictRightPostResolveLinkedMovePlay A strategy
      hwin initial entry input member env
    let projected := BlockRecordMonitor.projectReceiverPlay
      (profiledRawJointHybridFinitePayloadRowExactLeftReceiverProjection A)
      play
    ∃ past nextInput,
      (projected n).2.1.target row =
        ((profiledRawJointStrictRightPostResolveLinkedActivation A strategy
            hwin initial entry input member).target row past nextInput,
          (row,
            profiledRawJointStrictRightPostResolveLinkedChildren A strategy
              hwin initial entry input
              (.strict (profiledRawJointUnitLeftActualDirection row past
                nextInput)))) := by
  exact
    profiledRawJointLeftFinitePayloadLiteralPrefixMoveOfPlay_target_exists A
      (profiledRawJointStrictRightPostResolveLinkedActivation A strategy hwin
        initial entry input)
      (profiledRawJointStrictRightPostResolveLinkedChildren A strategy hwin
        initial entry input)
      (pairedLeftSenderStrategy
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictRightPairAt
          A strategy initial entry input).1.lambdaOfStrategy)
      (profiledRawJointStrictRightPostResolveLinkedActivation_sender_eq A
        strategy hwin initial entry input)
      member env n row

/-- Payload-only process-two corollary. -/
theorem profiledRawJointStrictRightPostResolveLinkedMovePlay_payload_exists
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) (env : Nat → In₁ × In₂) (n : Nat)
    (row : PairedEntryRow) :
    let play := profiledRawJointStrictRightPostResolveLinkedMovePlay A strategy
      hwin initial entry input member env
    let projected := BlockRecordMonitor.projectReceiverPlay
      (profiledRawJointHybridFinitePayloadRowExactLeftReceiverProjection A)
      play
    ∃ past nextInput,
      profiledRawJointHybridFinitePayloadLinkedTargetPayload A
          ((projected n).2.1.target row) =
        profiledRawJointStrictRightPostResolveLinkedChildren A strategy hwin
          initial entry input
          (.strict (profiledRawJointUnitLeftActualDirection row past
            nextInput)) := by
  dsimp only
  obtain ⟨past, nextInput, htarget⟩ :=
    profiledRawJointStrictRightPostResolveLinkedMovePlay_target_exists A
      strategy hwin initial entry input member env n row
  refine ⟨past, nextInput, ?_⟩
  rw [htarget]
  rfl

/-- Process-two arbitrary-prefix cut-root mirror. -/
theorem profiledRawJointStrictRightPostResolveLinkedMovePlay_cutRoot_exists
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) (env : Nat → In₁ × In₂) (n : Nat)
    (row : PairedEntryRow) :
    let play := profiledRawJointStrictRightPostResolveLinkedMovePlay A strategy
      hwin initial entry input member env
    let projected := BlockRecordMonitor.projectReceiverPlay
      (profiledRawJointHybridFinitePayloadRowExactLeftReceiverProjection A)
      play
    ∃ past nextInput,
      let actual := profiledRawJointUnitLeftActualDirection
        (In₁ := In₁) (In₂ := In₂) row past nextInput
      profiledRawJointHybridStrictPhysicalCutRoot A actual
          ((profiledRawJointHybridFinitePayloadLinkedTargetPayload A
            ((projected n).2.1.target row)) member) =
        profiledRawJointOneSidedCurrentSlots A .right
          ((projected n).2.1.target row).1 () := by
  dsimp only
  obtain ⟨past, nextInput, htarget⟩ :=
    profiledRawJointStrictRightPostResolveLinkedMovePlay_target_exists A
      strategy hwin initial entry input member env n row
  refine ⟨past, nextInput, ?_⟩
  rw [htarget]
  simpa using
    (profiledRawJointStrictRightPostResolveLinkedChildren_targetRoot A strategy
      hwin initial entry input member row past nextInput)

/-- Executable process-two handoff mirror. -/
theorem profiledRawJointStrictRightPostResolveLinkedMovePlay_installedMove_exists
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) (env : Nat → In₁ × In₂) (n : Nat)
    (row : PairedEntryRow) :
    let play := profiledRawJointStrictRightPostResolveLinkedMovePlay A strategy
      hwin initial entry input member env
    let projected := BlockRecordMonitor.projectReceiverPlay
      (profiledRawJointHybridFinitePayloadRowExactLeftReceiverProjection A)
      play
    ∃ (past : List (In₁ × In₂)) (nextInput : In₁ × In₂)
        (move : ProfiledRawJointRightPhysicalSiblingMove A),
      (profiledRawJointHybridFinitePayloadLinkedTargetPayload A
          ((projected n).2.1.target row) member).1 = some move ∧
      profiledRawJointOneSidedCurrentSlots A .right
          ((projected n).2.1.target row).1 () =
        some (.inl move.1.source) := by
  dsimp only
  obtain ⟨past, nextInput, htarget⟩ :=
    profiledRawJointStrictRightPostResolveLinkedMovePlay_target_exists A
      strategy hwin initial entry input member env n row
  obtain ⟨move, hmove, hroot⟩ :=
    profiledRawJointStrictRightPostResolveLinkedChildren_move_exists A strategy
      hwin initial entry input member row past nextInput
  refine ⟨past, nextInput, move, ?_, ?_⟩
  · rw [htarget]
    exact hmove
  · rw [htarget]
    exact hroot

/-- Arbitrary-depth semantic regeneration for the mirrored table. -/
theorem profiledRawJointStrictRightPostResolveLinkedMovePlay_targetPair_exists
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) (env : Nat → In₁ × In₂) (n : Nat)
    (row : PairedEntryRow) :
    let play := profiledRawJointStrictRightPostResolveLinkedMovePlay A strategy
      hwin initial entry input member env
    let projected := BlockRecordMonitor.projectReceiverPlay
      (profiledRawJointHybridFinitePayloadRowExactLeftReceiverProjection A)
      play
    ∃ (past : List (In₁ × In₂)) (nextInput : In₁ × In₂),
      let parent :=
        profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictRightPairAt
          A strategy initial entry input
      let child :=
        profiledRawLeftSemanticChildPair A parent row past nextInput
      ProcOnePendingOverlap child.1.leftHistory child.1.bothHistory ∧
        ((projected n).2.1.target row).1.family.right () =
          some (profiledRawRightSlotOfSemanticPair A child) := by
  dsimp only
  obtain ⟨past, nextInput, htarget⟩ :=
    profiledRawJointStrictRightPostResolveLinkedMovePlay_target_exists A
      strategy hwin initial entry input member env n row
  refine ⟨past, nextInput, ?_⟩
  have hpair :=
    profiledRawJointStrictRightPostResolveLinkedActivation_target_pair A
      strategy hwin initial entry input member row past nextInput
  rw [htarget]
  exact hpair

end

end DetParityAutomaton

end DistributedSynthesis
