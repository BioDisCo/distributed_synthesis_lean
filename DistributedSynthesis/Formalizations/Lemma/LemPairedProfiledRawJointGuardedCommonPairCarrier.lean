/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedPhysicalSiblingCoherence
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonTargetHandoff

/-!
# A finite represented pair of guarded common sibling moves

Choosing a fresh common representative from the post-`both` incidence code is
not sound: the representative may carry a different lambda.  The state below
therefore keeps the two *complete guarded finite moves*.  Its representation
witness is proof-only and says that the pair was extracted jointly from one
literal common world.  Since the data component is a pair of finite moves, the
resulting subtype is finite even though the witness mentions an unbounded
semantic history.

The successor operation chooses one witness for the current finite pair,
takes a literal simultaneous successor of that witness, and extracts the next
complete guarded pair.  Thus it never replaces a world merely because its
incidence code agrees.  The local root equations show that one pair of receive
transitions is simultaneously compatible with `both`, strict-right, and
strict-left.  No executable map accepts a graph, orientation, leader bit, or
semantic history.
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

private abbrev RightMove :=
  ProfiledRawJointGuardedRightPhysicalSiblingMove A

private abbrev LeftMove :=
  ProfiledRawJointGuardedLeftPhysicalSiblingMove A

/-! ## Extracting a guarded pair from one literal common world -/

noncomputable def profiledRawJointGuardedCommonRightMoveOfWorld
    (world : ProfiledRawJointCommonBaseWorld A strategy)
    (current : In₁ × In₂) : RightMove A :=
  profiledRawJointGuardedRightPhysicalSiblingMoveOf A hwin
    (profiledRawJointCommonWorldFamily A world)
    (profiledRawJointBothRestartDirection current)
    ((profiledRawJointCommonWorldAfterBoth A world current).procOneMember A)
    (profiledRawJointCommonWorld_semanticChild_right_bothRestart A world
      current)

noncomputable def profiledRawJointGuardedCommonLeftMoveOfWorld
    (world : ProfiledRawJointCommonBaseWorld A strategy)
    (current : In₁ × In₂) : LeftMove A :=
  profiledRawJointGuardedLeftPhysicalSiblingMoveOf A hwin
    (profiledRawJointCommonWorldFamily A world)
    (profiledRawJointBothRestartDirection current)
    ((profiledRawJointCommonWorldAfterBoth A world current).procTwoMember A)
    (profiledRawJointCommonWorld_semanticChild_left_bothRestart A world
      current)

/-- Proof-only joint representation of two complete guarded finite moves. -/
def ProfiledRawJointGuardedCommonPairRepresented
    (moves : RightMove A × LeftMove A) : Prop :=
  ∃ world : ProfiledRawJointCommonBaseWorld A strategy,
    ∃ current : In₁ × In₂,
      moves.1 = profiledRawJointGuardedCommonRightMoveOfWorld A strategy hwin
          world current ∧
        moves.2 = profiledRawJointGuardedCommonLeftMoveOfWorld A strategy hwin
          world current

/-- Runtime common state: two finite move identifiers plus a proof-erased
joint semantic representation. -/
abbrev ProfiledRawJointGuardedCommonPair :=
  { moves : RightMove A × LeftMove A //
    ProfiledRawJointGuardedCommonPairRepresented A strategy hwin moves }

noncomputable instance profiledRawJointGuardedCommonPairFintype :
    Fintype (ProfiledRawJointGuardedCommonPair A strategy hwin) := by
  classical
  infer_instance

/-- Canonical represented pair extracted from a literal world and input. -/
noncomputable def profiledRawJointGuardedCommonPairOfWorld
    (world : ProfiledRawJointCommonBaseWorld A strategy)
    (current : In₁ × In₂) :
    ProfiledRawJointGuardedCommonPair A strategy hwin :=
  ⟨(profiledRawJointGuardedCommonRightMoveOfWorld A strategy hwin world
      current,
    profiledRawJointGuardedCommonLeftMoveOfWorld A strategy hwin world
      current),
    ⟨world, current, rfl, rfl⟩⟩

/-- Fix one semantic representative for each represented finite move pair. -/
noncomputable def ProfiledRawJointGuardedCommonPair.representativeWorld
    (pair : ProfiledRawJointGuardedCommonPair A strategy hwin) :
    ProfiledRawJointCommonBaseWorld A strategy :=
  Classical.choose pair.property

noncomputable def ProfiledRawJointGuardedCommonPair.representativeCurrent
    (pair : ProfiledRawJointGuardedCommonPair A strategy hwin) : In₁ × In₂ :=
  Classical.choose (Classical.choose_spec pair.property)

theorem ProfiledRawJointGuardedCommonPair.right_eq_representative
    (pair : ProfiledRawJointGuardedCommonPair A strategy hwin) :
    pair.1.1 = profiledRawJointGuardedCommonRightMoveOfWorld A strategy hwin
      (pair.representativeWorld A strategy hwin)
      (pair.representativeCurrent A strategy hwin) :=
  (Classical.choose_spec
    (Classical.choose_spec pair.property)).1

theorem ProfiledRawJointGuardedCommonPair.left_eq_representative
    (pair : ProfiledRawJointGuardedCommonPair A strategy hwin) :
    pair.1.2 = profiledRawJointGuardedCommonLeftMoveOfWorld A strategy hwin
      (pair.representativeWorld A strategy hwin)
      (pair.representativeCurrent A strategy hwin) :=
  (Classical.choose_spec
    (Classical.choose_spec pair.property)).2

/-- One represented successor obtained from the chosen semantic witness.

This is an algebraic inhabitant, not an acceptance-preserving autonomous
transition: repeatedly re-choosing representatives can mosaic accepting
semantic plays.  The executable carrier below therefore takes its successor
pair from an explicit finite controller label. -/
noncomputable def ProfiledRawJointGuardedCommonPair.representativeAfterBoth
    (pair : ProfiledRawJointGuardedCommonPair A strategy hwin)
    (input : In₁ × In₂) :
    ProfiledRawJointGuardedCommonPair A strategy hwin :=
  profiledRawJointGuardedCommonPairOfWorld A strategy hwin
    (profiledRawJointCommonWorldAfterBoth A
      (pair.representativeWorld A strategy hwin)
      (pair.representativeCurrent A strategy hwin)) input

/-! ## The two controller roots below a represented pair -/

noncomputable def ProfiledRawJointGuardedCommonPair.rightRootRecord
    (pair : ProfiledRawJointGuardedCommonPair A strategy hwin)
    (input : In₁ × In₂) :=
  let move := pair.1.1
  let monitor := profiledRawJointGuardedRightPhysicalSiblingMonitor A move.1
    false
  let controller := move.memberController A false
  narrowedRecord monitor (controller.labeledTree []) monitor.initial
    (input.2, input.1)

noncomputable def ProfiledRawJointGuardedCommonPair.leftRootRecord
    (pair : ProfiledRawJointGuardedCommonPair A strategy hwin)
    (input : In₁ × In₂) :=
  let move := pair.1.2
  let monitor := profiledRawJointGuardedLeftPhysicalSiblingMonitor A move.1
    false
  let controller := move.memberController A false
  narrowedRecord monitor (controller.labeledTree []) monitor.initial input

/-- Anti-mosaic equation for process one at every represented pair.  It
compares the two receiver-side descriptions of a simultaneous output; the
blind strict sender output is intentionally not involved. -/
theorem ProfiledRawJointGuardedCommonPair.root_outputOne
    (pair : ProfiledRawJointGuardedCommonPair A strategy hwin)
    (input : In₁ × In₂) :
    (pair.rightRootRecord A strategy hwin input).2.1.physical.closingBoth =
      pairedLeftInformedForRow .both
        (pair.leftRootRecord A strategy hwin input).2.1.physical := by
  unfold ProfiledRawJointGuardedCommonPair.rightRootRecord
    ProfiledRawJointGuardedCommonPair.leftRootRecord
  rw [pair.right_eq_representative A strategy hwin,
    pair.left_eq_representative A strategy hwin]
  unfold profiledRawJointGuardedCommonRightMoveOfWorld
    profiledRawJointGuardedCommonLeftMoveOfWorld
  rw [profiledRawJointGuardedRightPhysicalSiblingMoveOf_root_record,
    profiledRawJointGuardedLeftPhysicalSiblingMoveOf_root_record]
  rfl

/-- Process-two receiver-side anti-mosaic equation. -/
theorem ProfiledRawJointGuardedCommonPair.root_outputTwo
    (pair : ProfiledRawJointGuardedCommonPair A strategy hwin)
    (input : In₁ × In₂) :
    (pair.leftRootRecord A strategy hwin input).2.1.physical.closingBoth =
      pairedRightInformedForRow .both
        (pair.rightRootRecord A strategy hwin input).2.1.physical := by
  unfold ProfiledRawJointGuardedCommonPair.rightRootRecord
    ProfiledRawJointGuardedCommonPair.leftRootRecord
  rw [pair.right_eq_representative A strategy hwin,
    pair.left_eq_representative A strategy hwin]
  unfold profiledRawJointGuardedCommonRightMoveOfWorld
    profiledRawJointGuardedCommonLeftMoveOfWorld
  rw [profiledRawJointGuardedRightPhysicalSiblingMoveOf_root_record,
    profiledRawJointGuardedLeftPhysicalSiblingMoveOf_root_record]
  rfl

/-- The two target labels emitted at the guarded roots reconstruct the exact
incidence code of the chosen representative's literal next common world.
This is a code theorem only; the occurrence-sensitive successor move remains
an explicit controller label below. -/
theorem ProfiledRawJointGuardedCommonPair.rootTargets_merge
    (pair : ProfiledRawJointGuardedCommonPair A strategy hwin)
    (input : In₁ × In₂) :
    profiledRawJointBothTargetMerge A input
        ((pair.rightRootRecord A strategy hwin input).2.1.target .both)
        ((pair.leftRootRecord A strategy hwin input).2.1.target .both) =
      (profiledRawJointCommonWorldFamily A
        (profiledRawJointCommonWorldAfterBoth A
          (profiledRawJointCommonWorldAfterBoth A
            (pair.representativeWorld A strategy hwin)
            (pair.representativeCurrent A strategy hwin)) input)
        ).incidenceCode A := by
  unfold ProfiledRawJointGuardedCommonPair.rightRootRecord
    ProfiledRawJointGuardedCommonPair.leftRootRecord
  rw [pair.right_eq_representative A strategy hwin,
    pair.left_eq_representative A strategy hwin]
  unfold profiledRawJointGuardedCommonRightMoveOfWorld
    profiledRawJointGuardedCommonLeftMoveOfWorld
  exact
    profiledRawJointGuardedSiblingControllerRootRecords_merge_eq_commonWorldAfterBoth
      A hwin
      (profiledRawJointCommonWorldFamily A
        (pair.representativeWorld A strategy hwin))
      (profiledRawJointBothRestartDirection
        (pair.representativeCurrent A strategy hwin))
      (profiledRawJointCommonWorldAfterBoth A
        (pair.representativeWorld A strategy hwin)
        (pair.representativeCurrent A strategy hwin))
      (profiledRawJointCommonWorld_semanticChild_eq_bothRestart A
        (pair.representativeWorld A strategy hwin)
        (pair.representativeCurrent A strategy hwin)) false false input

/-! ## Finite occurrence-sensitive common child labels -/

/-- A proposed next guarded pair is coherent when it has one joint semantic
representation whose source incidence is exactly the merge of the two
current root targets.  The existential witness is proof-only.  Requiring this
relation does not assert parity; an accepted rational/tree controller still
chooses the occurrence-sensitive child. -/
def ProfiledRawJointGuardedCommonSuccessorAllowed
    (pair : ProfiledRawJointGuardedCommonPair A strategy hwin)
    (input : In₁ × In₂)
    (next : ProfiledRawJointGuardedCommonPair A strategy hwin) : Prop :=
  ∃ world : ProfiledRawJointCommonBaseWorld A strategy,
    ∃ current : In₁ × In₂,
      next.1.1 = profiledRawJointGuardedCommonRightMoveOfWorld A strategy hwin
          world current ∧
        next.1.2 = profiledRawJointGuardedCommonLeftMoveOfWorld A strategy hwin
          world current ∧
        (profiledRawJointCommonWorldFamily A
          (profiledRawJointCommonWorldAfterBoth A world current)
          ).incidenceCode A =
        profiledRawJointBothTargetMerge A input
          ((pair.rightRootRecord A strategy hwin input).2.1.target .both)
          ((pair.leftRootRecord A strategy hwin input).2.1.target .both)

/-- Finite alphabet of complete coherent successor-pair labels. -/
abbrev ProfiledRawJointGuardedCommonSuccessor
    (pair : ProfiledRawJointGuardedCommonPair A strategy hwin)
    (input : In₁ × In₂) :=
  { next : ProfiledRawJointGuardedCommonPair A strategy hwin //
    ProfiledRawJointGuardedCommonSuccessorAllowed A strategy hwin pair input
      next }

noncomputable instance profiledRawJointGuardedCommonSuccessorFintype
    (pair : ProfiledRawJointGuardedCommonPair A strategy hwin)
    (input : In₁ × In₂) :
    Fintype (ProfiledRawJointGuardedCommonSuccessor A strategy hwin pair
      input) := by
  classical
  infer_instance

/-- The representative successor supplies one algebraic inhabitant of the
allowed alphabet.  A winning rational controller may select a different
allowed label at this occurrence. -/
noncomputable def
    ProfiledRawJointGuardedCommonPair.representativeSuccessor
    (pair : ProfiledRawJointGuardedCommonPair A strategy hwin)
    (input : In₁ × In₂) :
    ProfiledRawJointGuardedCommonSuccessor A strategy hwin pair input := by
  let world := profiledRawJointCommonWorldAfterBoth A
    (pair.representativeWorld A strategy hwin)
    (pair.representativeCurrent A strategy hwin)
  let next := profiledRawJointGuardedCommonPairOfWorld A strategy hwin world
    input
  refine ⟨next, world, input, rfl, rfl, ?_⟩
  exact (pair.rootTargets_merge A strategy hwin input).symm

theorem ProfiledRawJointGuardedCommonSuccessor.source_incidence
    {pair : ProfiledRawJointGuardedCommonPair A strategy hwin}
    {input : In₁ × In₂}
    (child : ProfiledRawJointGuardedCommonSuccessor A strategy hwin pair
      input) :
    ∃ world : ProfiledRawJointCommonBaseWorld A strategy,
      ∃ current : In₁ × In₂,
        child.1.1.1 =
            profiledRawJointGuardedCommonRightMoveOfWorld A strategy hwin world
              current ∧
          child.1.1.2 =
            profiledRawJointGuardedCommonLeftMoveOfWorld A strategy hwin world
              current ∧
          (profiledRawJointCommonWorldFamily A
            (profiledRawJointCommonWorldAfterBoth A world current)
            ).incidenceCode A =
          profiledRawJointBothTargetMerge A input
            ((pair.rightRootRecord A strategy hwin input).2.1.target .both)
            ((pair.leftRootRecord A strategy hwin input).2.1.target .both) :=
  child.property

/-! ## Local ambiguity shadows and strict owners -/

/-- Process one's result after an ambiguous receive.  `common` is the finite
next common pair; `source` and `strictReceiver` retain the strict-left
interpretation until the next delivered control resolves the ambiguity. -/
structure ProfiledRawJointGuardedCommonOneShadow where
  source : ProfiledRawJointGuardedCommonPair A strategy hwin
  common : ProfiledRawJointGuardedCommonPair A strategy hwin
  strictReceiver :
    (profiledRawJointGuardedLeftPhysicalSiblingMonitor A source.1.2.1 false
      ).State
  strictTarget : ProfiledRawJointUnitTarget A

/-- Process-two mirror retaining the strict-right interpretation. -/
structure ProfiledRawJointGuardedCommonTwoShadow where
  source : ProfiledRawJointGuardedCommonPair A strategy hwin
  common : ProfiledRawJointGuardedCommonPair A strategy hwin
  strictReceiver :
    (profiledRawJointGuardedRightPhysicalSiblingMonitor A source.1.1.1 false
      ).State
  strictTarget : ProfiledRawJointUnitTarget A

noncomputable instance profiledRawJointGuardedCommonOneShadowFintype :
    Fintype (ProfiledRawJointGuardedCommonOneShadow A strategy hwin) := by
  classical
  let Rep := Σ source : ProfiledRawJointGuardedCommonPair A strategy hwin,
    ProfiledRawJointGuardedCommonPair A strategy hwin ×
      (profiledRawJointGuardedLeftPhysicalSiblingMonitor A source.1.2.1 false
        ).State × ProfiledRawJointUnitTarget A
  let equiv : ProfiledRawJointGuardedCommonOneShadow A strategy hwin ≃ Rep := {
    toFun := fun state ↦
      ⟨state.source, state.common, state.strictReceiver, state.strictTarget⟩
    invFun := fun state ↦ ⟨state.1, state.2.1, state.2.2.1, state.2.2.2⟩
    left_inv := by intro state; cases state; rfl
    right_inv := by intro state; rcases state with ⟨a, b, c, d⟩; rfl }
  exact Fintype.ofEquiv Rep equiv.symm

noncomputable instance profiledRawJointGuardedCommonTwoShadowFintype :
    Fintype (ProfiledRawJointGuardedCommonTwoShadow A strategy hwin) := by
  classical
  let Rep := Σ source : ProfiledRawJointGuardedCommonPair A strategy hwin,
    ProfiledRawJointGuardedCommonPair A strategy hwin ×
      (profiledRawJointGuardedRightPhysicalSiblingMonitor A source.1.1.1 false
        ).State × ProfiledRawJointUnitTarget A
  let equiv : ProfiledRawJointGuardedCommonTwoShadow A strategy hwin ≃ Rep := {
    toFun := fun state ↦
      ⟨state.source, state.common, state.strictReceiver, state.strictTarget⟩
    invFun := fun state ↦ ⟨state.1, state.2.1, state.2.2.1, state.2.2.2⟩
    left_inv := by intro state; cases state; rfl
    right_inv := by intro state; rcases state with ⟨a, b, c, d⟩; rfl }
  exact Fintype.ofEquiv Rep equiv.symm

/-- Process one's receive transition at the unresolved common/strict-left
fork. -/
noncomputable def profiledRawJointGuardedCommonStartOneShadow
    (pair : ProfiledRawJointGuardedCommonPair A strategy hwin)
    (next : ProfiledRawJointGuardedCommonPair A strategy hwin)
    (input : In₁ × In₂) :
    Out₁ × ProfiledRawJointGuardedCommonOneShadow A strategy hwin :=
  let move := pair.1.2
  let monitor := profiledRawJointGuardedLeftPhysicalSiblingMonitor A move.1
    false
  let record := pair.leftRootRecord A strategy hwin input
  (pairedLeftInformedForRow .both record.2.1.physical,
    ⟨pair, next, monitor.step monitor.initial record,
      record.2.1.target .both⟩)

/-- Process-two receive mirror. -/
noncomputable def profiledRawJointGuardedCommonStartTwoShadow
    (pair : ProfiledRawJointGuardedCommonPair A strategy hwin)
    (next : ProfiledRawJointGuardedCommonPair A strategy hwin)
    (input : In₁ × In₂) :
    Out₂ × ProfiledRawJointGuardedCommonTwoShadow A strategy hwin :=
  let move := pair.1.1
  let monitor := profiledRawJointGuardedRightPhysicalSiblingMonitor A move.1
    false
  let record := pair.rightRootRecord A strategy hwin input
  (pairedRightInformedForRow .both record.2.1.physical,
    ⟨pair, next, monitor.step monitor.initial record,
      record.2.1.target .both⟩)

/-- Public process-one receive constructor driven by one allowed complete
successor-pair label from the rational controller. -/
noncomputable def
    profiledRawJointGuardedCommonStartOneShadowOfSuccessor
    (pair : ProfiledRawJointGuardedCommonPair A strategy hwin)
    (input : In₁ × In₂)
    (child : ProfiledRawJointGuardedCommonSuccessor A strategy hwin pair
      input) :
    Out₁ × ProfiledRawJointGuardedCommonOneShadow A strategy hwin :=
  profiledRawJointGuardedCommonStartOneShadow A strategy hwin pair child.1
    input

/-- Process-two mirror, consuming the same allowed child label. -/
noncomputable def
    profiledRawJointGuardedCommonStartTwoShadowOfSuccessor
    (pair : ProfiledRawJointGuardedCommonPair A strategy hwin)
    (input : In₁ × In₂)
    (child : ProfiledRawJointGuardedCommonSuccessor A strategy hwin pair
      input) :
    Out₂ × ProfiledRawJointGuardedCommonTwoShadow A strategy hwin :=
  profiledRawJointGuardedCommonStartTwoShadow A strategy hwin pair child.1
    input

@[simp] theorem
    profiledRawJointGuardedCommonStartOneShadowOfSuccessor_source
    (pair : ProfiledRawJointGuardedCommonPair A strategy hwin)
    (input : In₁ × In₂)
    (child : ProfiledRawJointGuardedCommonSuccessor A strategy hwin pair
      input) :
    (profiledRawJointGuardedCommonStartOneShadowOfSuccessor A strategy hwin
      pair input child).2.source = pair :=
  rfl

@[simp] theorem
    profiledRawJointGuardedCommonStartOneShadowOfSuccessor_common
    (pair : ProfiledRawJointGuardedCommonPair A strategy hwin)
    (input : In₁ × In₂)
    (child : ProfiledRawJointGuardedCommonSuccessor A strategy hwin pair
      input) :
    (profiledRawJointGuardedCommonStartOneShadowOfSuccessor A strategy hwin
      pair input child).2.common = child.1 :=
  rfl

@[simp] theorem
    profiledRawJointGuardedCommonStartTwoShadowOfSuccessor_source
    (pair : ProfiledRawJointGuardedCommonPair A strategy hwin)
    (input : In₁ × In₂)
    (child : ProfiledRawJointGuardedCommonSuccessor A strategy hwin pair
      input) :
    (profiledRawJointGuardedCommonStartTwoShadowOfSuccessor A strategy hwin
      pair input child).2.source = pair :=
  rfl

@[simp] theorem
    profiledRawJointGuardedCommonStartTwoShadowOfSuccessor_common
    (pair : ProfiledRawJointGuardedCommonPair A strategy hwin)
    (input : In₁ × In₂)
    (child : ProfiledRawJointGuardedCommonSuccessor A strategy hwin pair
      input) :
    (profiledRawJointGuardedCommonStartTwoShadowOfSuccessor A strategy hwin
      pair input child).2.common = child.1 :=
  rfl

theorem profiledRawJointGuardedCommonStartSuccessorShadows_agree
    (pair : ProfiledRawJointGuardedCommonPair A strategy hwin)
    (input : In₁ × In₂)
    (child : ProfiledRawJointGuardedCommonSuccessor A strategy hwin pair
      input) :
    (profiledRawJointGuardedCommonStartOneShadowOfSuccessor A strategy hwin
      pair input child).2.common =
      (profiledRawJointGuardedCommonStartTwoShadowOfSuccessor A strategy hwin
        pair input child).2.common :=
  rfl

/-- Process-one strict-right owner below the same represented finite pair. -/
noncomputable abbrev ProfiledRawJointGuardedCommonRightOwner :=
  Sigma fun source : ProfiledRawJointGuardedCommonPair A strategy hwin ↦
    ((source.1.1).memberController A false).Control

/-- Process-two strict-left owner. -/
noncomputable abbrev ProfiledRawJointGuardedCommonLeftOwner :=
  Sigma fun source : ProfiledRawJointGuardedCommonPair A strategy hwin ↦
    ((source.1.2).memberController A false).Control

noncomputable instance profiledRawJointGuardedCommonRightOwnerFintype :
    Fintype (ProfiledRawJointGuardedCommonRightOwner A strategy hwin) := by
  classical
  infer_instance

noncomputable instance profiledRawJointGuardedCommonLeftOwnerFintype :
    Fintype (ProfiledRawJointGuardedCommonLeftOwner A strategy hwin) := by
  classical
  infer_instance

noncomputable def profiledRawJointGuardedCommonNoRecvOne
    (pair : ProfiledRawJointGuardedCommonPair A strategy hwin) (input : In₁) :
    Out₁ × ProfiledRawJointGuardedCommonRightOwner A strategy hwin :=
  let controller := (pair.1.1).memberController A false
  let label := controller.labelOf controller.initial
  (label.1 input, ⟨pair, controller.step controller.initial input⟩)

noncomputable def profiledRawJointGuardedCommonNoRecvTwo
    (pair : ProfiledRawJointGuardedCommonPair A strategy hwin) (input : In₂) :
    Out₂ × ProfiledRawJointGuardedCommonLeftOwner A strategy hwin :=
  let controller := (pair.1.2).memberController A false
  let label := controller.labelOf controller.initial
  (label.1 input, ⟨pair, controller.step controller.initial input⟩)

/-- The same two receive transitions implement a genuine simultaneous root. -/
theorem profiledRawJointGuardedCommonStartShadows_both_pair
    (pair : ProfiledRawJointGuardedCommonPair A strategy hwin)
    (next : ProfiledRawJointGuardedCommonPair A strategy hwin)
    (input : In₁ × In₂) :
    ((profiledRawJointGuardedCommonStartOneShadow A strategy hwin pair next
        input).1,
      (profiledRawJointGuardedCommonStartTwoShadow A strategy hwin pair next
        input).1) =
      (pairedLeftInformedForRow .both
          (pair.leftRootRecord A strategy hwin input).2.1.physical,
        pairedRightInformedForRow .both
          (pair.rightRootRecord A strategy hwin input).2.1.physical) :=
  rfl

/-- If process one observes `noRecv`, its output and process two's unchanged
receive transition are exactly the two projections of the right root record. -/
theorem profiledRawJointGuardedCommon_strictRight_root_pair
    (pair : ProfiledRawJointGuardedCommonPair A strategy hwin)
    (next : ProfiledRawJointGuardedCommonPair A strategy hwin)
    (input : In₁ × In₂) :
    ((profiledRawJointGuardedCommonNoRecvOne A strategy hwin pair input.1).1,
      (profiledRawJointGuardedCommonStartTwoShadow A strategy hwin pair next
        input).1) =
      ((pair.rightRootRecord A strategy hwin input).2.2,
        pairedRightInformedForRow .both
          (pair.rightRootRecord A strategy hwin input).2.1.physical) :=
  rfl

/-- Strict-left mirror. -/
theorem profiledRawJointGuardedCommon_strictLeft_root_pair
    (pair : ProfiledRawJointGuardedCommonPair A strategy hwin)
    (next : ProfiledRawJointGuardedCommonPair A strategy hwin)
    (input : In₁ × In₂) :
    ((profiledRawJointGuardedCommonStartOneShadow A strategy hwin pair next
        input).1,
      (profiledRawJointGuardedCommonNoRecvTwo A strategy hwin pair input.2).1)
      =
      (pairedLeftInformedForRow .both
          (pair.leftRootRecord A strategy hwin input).2.1.physical,
        (pair.leftRootRecord A strategy hwin input).2.2) :=
  rfl

/-- The two independently executable receive transitions give the two
closing projections of one simultaneous root.  This is the dangerous
receiver-side common/strict pair test.  No equality with either blind sender
output is asserted or required. -/
theorem profiledRawJointGuardedCommon_root_receiver_pair_coherent
    (pair : ProfiledRawJointGuardedCommonPair A strategy hwin)
    (next : ProfiledRawJointGuardedCommonPair A strategy hwin)
    (input : In₁ × In₂) :
    ((profiledRawJointGuardedCommonStartOneShadow A strategy hwin pair next
        input).1,
      (profiledRawJointGuardedCommonStartTwoShadow A strategy hwin pair next
        input).1) =
      ((pair.rightRootRecord A strategy hwin input).2.1.physical.closingBoth,
        (pair.leftRootRecord A strategy hwin input).2.1.physical.closingBoth) :=
  Prod.ext
    (pair.root_outputOne A strategy hwin input).symm
    (pair.root_outputTwo A strategy hwin input).symm

/-- Allowed-child form of the dangerous receiver pair equation. -/
theorem profiledRawJointGuardedCommonStartSuccessorShadows_outputs
    (pair : ProfiledRawJointGuardedCommonPair A strategy hwin)
    (input : In₁ × In₂)
    (child : ProfiledRawJointGuardedCommonSuccessor A strategy hwin pair
      input) :
    ((profiledRawJointGuardedCommonStartOneShadowOfSuccessor A strategy hwin
        pair input child).1,
      (profiledRawJointGuardedCommonStartTwoShadowOfSuccessor A strategy hwin
        pair input child).1) =
      ((pair.rightRootRecord A strategy hwin input).2.1.physical.closingBoth,
        (pair.leftRootRecord A strategy hwin input).2.1.physical.closingBoth) :=
  profiledRawJointGuardedCommon_root_receiver_pair_coherent A strategy hwin
    pair child.1 input

/-! ## Repeated simultaneous rounds and first strict exits -/

/-- Proof-side agreement of the finite common pair stored by the two local
shadows.  It is an invariant, not an executable test. -/
def ProfiledRawJointGuardedCommonShadowsAgree
    (one : ProfiledRawJointGuardedCommonOneShadow A strategy hwin)
    (two : ProfiledRawJointGuardedCommonTwoShadow A strategy hwin) : Prop :=
  one.common = two.common

/-- On another receive, process one uses only its locally stored common pair;
the delivered shadow certifies the reachable phase but is not inspected. -/
noncomputable def profiledRawJointGuardedCommonOneShadowRecvTwoShadow
    (one : ProfiledRawJointGuardedCommonOneShadow A strategy hwin)
    (_two : ProfiledRawJointGuardedCommonTwoShadow A strategy hwin)
    (next : ProfiledRawJointGuardedCommonPair A strategy hwin)
    (own : In₁) (delivered : In₂) :
    Out₁ × ProfiledRawJointGuardedCommonOneShadow A strategy hwin :=
  profiledRawJointGuardedCommonStartOneShadow A strategy hwin one.common next
    (own, delivered)

/-- Process-two mirror. -/
noncomputable def profiledRawJointGuardedCommonTwoShadowRecvOneShadow
    (two : ProfiledRawJointGuardedCommonTwoShadow A strategy hwin)
    (_one : ProfiledRawJointGuardedCommonOneShadow A strategy hwin)
    (next : ProfiledRawJointGuardedCommonPair A strategy hwin)
    (own : In₂) (delivered : In₁) :
    Out₂ × ProfiledRawJointGuardedCommonTwoShadow A strategy hwin :=
  profiledRawJointGuardedCommonStartTwoShadow A strategy hwin two.common next
    (delivered, own)

/-- A simultaneous round preserves agreement of the finite guarded pair. -/
theorem profiledRawJointGuardedCommonShadowRecvShadows_agree
    (one : ProfiledRawJointGuardedCommonOneShadow A strategy hwin)
    (two : ProfiledRawJointGuardedCommonTwoShadow A strategy hwin)
    (next : ProfiledRawJointGuardedCommonPair A strategy hwin)
    (input : In₁ × In₂) :
    ProfiledRawJointGuardedCommonShadowsAgree A strategy hwin
      (profiledRawJointGuardedCommonOneShadowRecvTwoShadow A strategy hwin one
        two next input.1 input.2).2
      (profiledRawJointGuardedCommonTwoShadowRecvOneShadow A strategy hwin two
        one next input.2 input.1).2 := by
  unfold ProfiledRawJointGuardedCommonShadowsAgree
  dsimp [profiledRawJointGuardedCommonOneShadowRecvTwoShadow,
    profiledRawJointGuardedCommonTwoShadowRecvOneShadow,
    profiledRawJointGuardedCommonStartOneShadow,
    profiledRawJointGuardedCommonStartTwoShadow]

/-- The repeated-`both` output is again the receiver-coherent root pair of
one finite represented common state. -/
theorem profiledRawJointGuardedCommonShadowRecvShadows_outputs
    (one : ProfiledRawJointGuardedCommonOneShadow A strategy hwin)
    (two : ProfiledRawJointGuardedCommonTwoShadow A strategy hwin)
    (hagrees : ProfiledRawJointGuardedCommonShadowsAgree A strategy hwin one
      two)
    (next : ProfiledRawJointGuardedCommonPair A strategy hwin)
    (input : In₁ × In₂) :
    ((profiledRawJointGuardedCommonOneShadowRecvTwoShadow A strategy hwin one
        two next input.1 input.2).1,
      (profiledRawJointGuardedCommonTwoShadowRecvOneShadow A strategy hwin two
        one next input.2 input.1).1) =
      ((one.common.rightRootRecord A strategy hwin input).2.1.physical.closingBoth,
        (one.common.leftRootRecord A strategy hwin input).2.1.physical.closingBoth) := by
  unfold ProfiledRawJointGuardedCommonShadowsAgree at hagrees
  unfold profiledRawJointGuardedCommonOneShadowRecvTwoShadow
    profiledRawJointGuardedCommonTwoShadowRecvOneShadow
  rw [← hagrees]
  exact profiledRawJointGuardedCommon_root_receiver_pair_coherent A strategy
    hwin one.common next input

/-- A local no-receive from process one starts the right guarded controller
stored in its finite common branch. -/
noncomputable def profiledRawJointGuardedCommonOneShadowNoRecv
    (one : ProfiledRawJointGuardedCommonOneShadow A strategy hwin)
    (input : In₁) :
    Out₁ × ProfiledRawJointGuardedCommonRightOwner A strategy hwin :=
  profiledRawJointGuardedCommonNoRecvOne A strategy hwin one.common input

/-- Process-two strict-left mirror. -/
noncomputable def profiledRawJointGuardedCommonTwoShadowNoRecv
    (two : ProfiledRawJointGuardedCommonTwoShadow A strategy hwin)
    (input : In₂) :
    Out₂ × ProfiledRawJointGuardedCommonLeftOwner A strategy hwin :=
  profiledRawJointGuardedCommonNoRecvTwo A strategy hwin two.common input

/-- If the agreed shadows take a first strict-right exit, the blind owner and
the unchanged receiver transition are the two parts of one guarded record. -/
theorem profiledRawJointGuardedCommonShadows_strictRight_root_pair
    (one : ProfiledRawJointGuardedCommonOneShadow A strategy hwin)
    (two : ProfiledRawJointGuardedCommonTwoShadow A strategy hwin)
    (hagrees : ProfiledRawJointGuardedCommonShadowsAgree A strategy hwin one
      two)
    (next : ProfiledRawJointGuardedCommonPair A strategy hwin)
    (input : In₁ × In₂) :
    ((profiledRawJointGuardedCommonOneShadowNoRecv A strategy hwin one
        input.1).1,
      (profiledRawJointGuardedCommonTwoShadowRecvOneShadow A strategy hwin two
        one next input.2 input.1).1) =
      ((one.common.rightRootRecord A strategy hwin input).2.2,
        pairedRightInformedForRow .both
          (one.common.rightRootRecord A strategy hwin input).2.1.physical) := by
  unfold ProfiledRawJointGuardedCommonShadowsAgree at hagrees
  unfold profiledRawJointGuardedCommonOneShadowNoRecv
    profiledRawJointGuardedCommonTwoShadowRecvOneShadow
  rw [← hagrees]
  exact profiledRawJointGuardedCommon_strictRight_root_pair A strategy hwin
    one.common next input

/-- Strict-left mirror. -/
theorem profiledRawJointGuardedCommonShadows_strictLeft_root_pair
    (one : ProfiledRawJointGuardedCommonOneShadow A strategy hwin)
    (two : ProfiledRawJointGuardedCommonTwoShadow A strategy hwin)
    (hagrees : ProfiledRawJointGuardedCommonShadowsAgree A strategy hwin one
      two)
    (next : ProfiledRawJointGuardedCommonPair A strategy hwin)
    (input : In₁ × In₂) :
    ((profiledRawJointGuardedCommonOneShadowRecvTwoShadow A strategy hwin one
        two next input.1 input.2).1,
      (profiledRawJointGuardedCommonTwoShadowNoRecv A strategy hwin two
        input.2).1) =
      (pairedLeftInformedForRow .both
          (one.common.leftRootRecord A strategy hwin input).2.1.physical,
        (one.common.leftRootRecord A strategy hwin input).2.2) := by
  unfold ProfiledRawJointGuardedCommonShadowsAgree at hagrees
  unfold profiledRawJointGuardedCommonOneShadowRecvTwoShadow
    profiledRawJointGuardedCommonTwoShadowNoRecv
  rw [← hagrees]
  exact profiledRawJointGuardedCommon_strictLeft_root_pair A strategy hwin
    one.common next input

/-! ## Resolution by a delivered strict owner -/

/-- Align a delivered strict-left owner with process one's stored source.
The mismatch branch is unreachable from an agreed start and merely totalizes
the local transition table. -/
noncomputable def profiledRawJointGuardedCommonLeftOwnerFor
    (one : ProfiledRawJointGuardedCommonOneShadow A strategy hwin)
    (owner : ProfiledRawJointGuardedCommonLeftOwner A strategy hwin) :
    ((one.source.1.2).memberController A false).Control := by
  classical
  exact if h : owner.1 = one.source then h ▸ owner.2
    else ((one.source.1.2).memberController A false).initial

/-- Process-two/right mirror alignment. -/
noncomputable def profiledRawJointGuardedCommonRightOwnerFor
    (two : ProfiledRawJointGuardedCommonTwoShadow A strategy hwin)
    (owner : ProfiledRawJointGuardedCommonRightOwner A strategy hwin) :
    ((two.source.1.1).memberController A false).Control := by
  classical
  exact if h : owner.1 = two.source then h ▸ owner.2
    else ((two.source.1.1).memberController A false).initial

/-- Finite process-one state after a delivered strict-left owner resolves the
common/strict ambiguity. -/
noncomputable abbrev ProfiledRawJointGuardedCommonLeftStrictReceiver :=
  Sigma fun source : ProfiledRawJointGuardedCommonPair A strategy hwin ↦
    (profiledRawJointGuardedLeftPhysicalSiblingMonitor A source.1.2.1 false
      ).State × Option (ProfiledRawJointUnitTarget A)

/-- Process-two strict-right receiver. -/
noncomputable abbrev ProfiledRawJointGuardedCommonRightStrictReceiver :=
  Sigma fun source : ProfiledRawJointGuardedCommonPair A strategy hwin ↦
    (profiledRawJointGuardedRightPhysicalSiblingMonitor A source.1.1.1 false
      ).State × Option (ProfiledRawJointUnitTarget A)

noncomputable instance profiledRawJointGuardedCommonLeftStrictReceiverFintype :
    Fintype
      (ProfiledRawJointGuardedCommonLeftStrictReceiver A strategy hwin) := by
  classical
  infer_instance

noncomputable instance profiledRawJointGuardedCommonRightStrictReceiverFintype :
    Fintype
      (ProfiledRawJointGuardedCommonRightStrictReceiver A strategy hwin) := by
  classical
  infer_instance

/-- The delivered owner advances the exact left controller and exposes its
checked finite target. -/
noncomputable def profiledRawJointGuardedCommonOneShadowRecvLeftOwner
    (one : ProfiledRawJointGuardedCommonOneShadow A strategy hwin)
    (owner : ProfiledRawJointGuardedCommonLeftOwner A strategy hwin)
    (own : In₁) (delivered : In₂) :
    Out₁ × ProfiledRawJointGuardedCommonLeftStrictReceiver A strategy hwin :=
  let move := one.source.1.2
  let monitor := profiledRawJointGuardedLeftPhysicalSiblingMonitor A move.1
    false
  let controller := move.memberController A false
  let ownerControl := profiledRawJointGuardedCommonLeftOwnerFor A strategy hwin
    one owner
  let label := controller.labelOf ownerControl
  let output := label.2 one.strictReceiver (own, delivered)
  let nextState := monitor.step one.strictReceiver
    ((own, delivered), output, label.1 delivered)
  (pairedLeftInformedForRow .both output.physical,
    ⟨one.source, nextState, some (output.target .both)⟩)

/-- Delivered right-owner mirror. -/
noncomputable def profiledRawJointGuardedCommonTwoShadowRecvRightOwner
    (two : ProfiledRawJointGuardedCommonTwoShadow A strategy hwin)
    (owner : ProfiledRawJointGuardedCommonRightOwner A strategy hwin)
    (own : In₂) (delivered : In₁) :
    Out₂ × ProfiledRawJointGuardedCommonRightStrictReceiver A strategy hwin :=
  let move := two.source.1.1
  let monitor := profiledRawJointGuardedRightPhysicalSiblingMonitor A move.1
    false
  let controller := move.memberController A false
  let ownerControl := profiledRawJointGuardedCommonRightOwnerFor A strategy
    hwin two owner
  let label := controller.labelOf ownerControl
  let output := label.2 two.strictReceiver (own, delivered)
  let nextState := monitor.step two.strictReceiver
    ((own, delivered), output, label.1 delivered)
  (pairedRightInformedForRow .both output.physical,
    ⟨two.source, nextState, some (output.target .both)⟩)

@[simp] theorem profiledRawJointGuardedCommonOneShadowRecvLeftOwner_source
    (one : ProfiledRawJointGuardedCommonOneShadow A strategy hwin)
    (owner : ProfiledRawJointGuardedCommonLeftOwner A strategy hwin)
    (own : In₁) (delivered : In₂) :
    (profiledRawJointGuardedCommonOneShadowRecvLeftOwner A strategy hwin one
      owner own delivered).2.1 = one.source :=
  rfl

@[simp] theorem profiledRawJointGuardedCommonTwoShadowRecvRightOwner_source
    (two : ProfiledRawJointGuardedCommonTwoShadow A strategy hwin)
    (owner : ProfiledRawJointGuardedCommonRightOwner A strategy hwin)
    (own : In₂) (delivered : In₁) :
    (profiledRawJointGuardedCommonTwoShadowRecvRightOwner A strategy hwin two
      owner own delivered).2.1 = two.source :=
  rfl

/-! ## Continuing a resolved strict block -/

/-- Blind process-one step inside a strict-right block. -/
noncomputable def profiledRawJointGuardedCommonRightOwnerNoRecv
    (owner : ProfiledRawJointGuardedCommonRightOwner A strategy hwin)
    (input : In₁) :
    Out₁ × ProfiledRawJointGuardedCommonRightOwner A strategy hwin :=
  let controller := (owner.1.1.1).memberController A false
  let label := controller.labelOf owner.2
  (label.1 input, ⟨owner.1, controller.step owner.2 input⟩)

/-- Blind process-two step inside a strict-left block. -/
noncomputable def profiledRawJointGuardedCommonLeftOwnerNoRecv
    (owner : ProfiledRawJointGuardedCommonLeftOwner A strategy hwin)
    (input : In₂) :
    Out₂ × ProfiledRawJointGuardedCommonLeftOwner A strategy hwin :=
  let controller := (owner.1.1.2).memberController A false
  let label := controller.labelOf owner.2
  (label.1 input, ⟨owner.1, controller.step owner.2 input⟩)

@[simp] theorem profiledRawJointGuardedCommonRightOwnerNoRecv_source
    (owner : ProfiledRawJointGuardedCommonRightOwner A strategy hwin)
    (input : In₁) :
    (profiledRawJointGuardedCommonRightOwnerNoRecv A strategy hwin owner
      input).2.1 = owner.1 :=
  rfl

@[simp] theorem profiledRawJointGuardedCommonLeftOwnerNoRecv_source
    (owner : ProfiledRawJointGuardedCommonLeftOwner A strategy hwin)
    (input : In₂) :
    (profiledRawJointGuardedCommonLeftOwnerNoRecv A strategy hwin owner
      input).2.1 = owner.1 :=
  rfl

/-- Totalize alignment of a delivered right owner at an already resolved
right receiver. -/
noncomputable def profiledRawJointGuardedCommonRightStrictOwnerFor
    (receiver : ProfiledRawJointGuardedCommonRightStrictReceiver A strategy
      hwin)
    (owner : ProfiledRawJointGuardedCommonRightOwner A strategy hwin) :
    ((receiver.1.1.1).memberController A false).Control := by
  classical
  exact if h : owner.1 = receiver.1 then h ▸ owner.2
    else ((receiver.1.1.1).memberController A false).initial

/-- Left mirror. -/
noncomputable def profiledRawJointGuardedCommonLeftStrictOwnerFor
    (receiver : ProfiledRawJointGuardedCommonLeftStrictReceiver A strategy
      hwin)
    (owner : ProfiledRawJointGuardedCommonLeftOwner A strategy hwin) :
    ((receiver.1.1.2).memberController A false).Control := by
  classical
  exact if h : owner.1 = receiver.1 then h ▸ owner.2
    else ((receiver.1.1.2).memberController A false).initial

/-- Continue a resolved strict-right receiver, retaining the latest checked
target for the close handoff. -/
noncomputable def profiledRawJointGuardedCommonRightStrictReceiverRecvOwner
    (receiver : ProfiledRawJointGuardedCommonRightStrictReceiver A strategy
      hwin)
    (owner : ProfiledRawJointGuardedCommonRightOwner A strategy hwin)
    (own : In₂) (delivered : In₁) :
    Out₂ × ProfiledRawJointGuardedCommonRightStrictReceiver A strategy hwin :=
  let move := receiver.1.1.1
  let monitor := profiledRawJointGuardedRightPhysicalSiblingMonitor A move.1
    false
  let controller := move.memberController A false
  let ownerControl := profiledRawJointGuardedCommonRightStrictOwnerFor A
    strategy hwin receiver owner
  let label := controller.labelOf ownerControl
  let output := label.2 receiver.2.1 (own, delivered)
  let nextState := monitor.step receiver.2.1
    ((own, delivered), output, label.1 delivered)
  (pairedRightInformedForRow .both output.physical,
    ⟨receiver.1, nextState, some (output.target .both)⟩)

/-- Continue a resolved strict-left receiver. -/
noncomputable def profiledRawJointGuardedCommonLeftStrictReceiverRecvOwner
    (receiver : ProfiledRawJointGuardedCommonLeftStrictReceiver A strategy
      hwin)
    (owner : ProfiledRawJointGuardedCommonLeftOwner A strategy hwin)
    (own : In₁) (delivered : In₂) :
    Out₁ × ProfiledRawJointGuardedCommonLeftStrictReceiver A strategy hwin :=
  let move := receiver.1.1.2
  let monitor := profiledRawJointGuardedLeftPhysicalSiblingMonitor A move.1
    false
  let controller := move.memberController A false
  let ownerControl := profiledRawJointGuardedCommonLeftStrictOwnerFor A
    strategy hwin receiver owner
  let label := controller.labelOf ownerControl
  let output := label.2 receiver.2.1 (own, delivered)
  let nextState := monitor.step receiver.2.1
    ((own, delivered), output, label.1 delivered)
  (pairedLeftInformedForRow .both output.physical,
    ⟨receiver.1, nextState, some (output.target .both)⟩)

@[simp] theorem
    profiledRawJointGuardedCommonRightStrictReceiverRecvOwner_source
    (receiver : ProfiledRawJointGuardedCommonRightStrictReceiver A strategy
      hwin)
    (owner : ProfiledRawJointGuardedCommonRightOwner A strategy hwin)
    (own : In₂) (delivered : In₁) :
    (profiledRawJointGuardedCommonRightStrictReceiverRecvOwner A strategy hwin
      receiver owner own delivered).2.1 = receiver.1 :=
  rfl

@[simp] theorem
    profiledRawJointGuardedCommonLeftStrictReceiverRecvOwner_source
    (receiver : ProfiledRawJointGuardedCommonLeftStrictReceiver A strategy
      hwin)
    (owner : ProfiledRawJointGuardedCommonLeftOwner A strategy hwin)
    (own : In₁) (delivered : In₂) :
    (profiledRawJointGuardedCommonLeftStrictReceiverRecvOwner A strategy hwin
      receiver owner own delivered).2.1 = receiver.1 :=
  rfl

/-- The initial ambiguous receive retains the exact root target needed if the
next delivery reveals that the round was strict-left. -/
@[simp] theorem profiledRawJointGuardedCommonStartOneShadow_target
    (pair next : ProfiledRawJointGuardedCommonPair A strategy hwin)
    (input : In₁ × In₂) :
    (profiledRawJointGuardedCommonStartOneShadow A strategy hwin pair next
      input).2.strictTarget =
      (pair.leftRootRecord A strategy hwin input).2.1.target .both :=
  rfl

/-- Strict-right mirror. -/
@[simp] theorem profiledRawJointGuardedCommonStartTwoShadow_target
    (pair next : ProfiledRawJointGuardedCommonPair A strategy hwin)
    (input : In₁ × In₂) :
    (profiledRawJointGuardedCommonStartTwoShadow A strategy hwin pair next
      input).2.strictTarget =
      (pair.rightRootRecord A strategy hwin input).2.1.target .both :=
  rfl

end

end DetParityAutomaton

end DistributedSynthesis
