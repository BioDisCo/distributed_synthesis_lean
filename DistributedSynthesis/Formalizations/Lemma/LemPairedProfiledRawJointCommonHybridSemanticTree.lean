/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointCommonBothRestart
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedSemanticTree

/-!
# The common-prefix/one-sided raw semantic tree

Before the first strict round, neither process can know which strict
orientation will eventually occur.  The exact semantic state therefore keeps
the two projections of one literal common world.  A simultaneous round stays
in that common mode.  The first strict proof-side direction selects one
one-sided child, after which the already proved recursively exact one-sided
tree takes over.

The input-free tree interface is total, so a simultaneous direction offered
after the strict exit is sent to a distinguished dead mode.  The finite code
and move types are tagged by this mode.  Thus the dead completion is legal by
definition and self-loops; it does not ask for a fake raw lambda at an
unreachable semantic state.

The side and pivot normalization below are proof-tree data.  They are never
provided to either process.  In particular, no node is assumed to know the
strict leader.
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

/-! ## Proof-tree directions -/

/-- A physical simultaneous continuation, or the first/later strict
proof-side block direction. -/
inductive ProfiledRawJointHybridDirection where
  | simultaneous (input : In₁ × In₂)
  | strict (actual : ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))

instance profiledRawJointHybridDirectionNonempty :
    Nonempty (ProfiledRawJointHybridDirection
      (In₁ := In₁) (In₂ := In₂)) :=
  ⟨.simultaneous (default, default)⟩

/-- At a common world the unique lineage pivot is the shared `.both` row.
All scan and closing-input data are retained. -/
def profiledRawJointForceBothPivots
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂) :=
  { direction with
    rightPivot := ((), .both)
    leftPivot := ((), .both) }

/-- Strict actual direction with the common-world pivots normalized. -/
def profiledRawJointCommonActualDirection
    (actual : ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂) :=
  { side := actual.side
    direction := profiledRawJointForceBothPivots actual.direction }

section
omit [Inhabited In₁] [Inhabited In₂] [Fintype In₁] [Fintype In₂]

@[simp] theorem profiledRawJointCommonActualDirection_side
    (actual : ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    (profiledRawJointCommonActualDirection actual).side = actual.side :=
  rfl

@[simp] theorem profiledRawJointCommonActualDirection_rightPivot_row
    (actual : ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    (profiledRawJointCommonActualDirection actual).direction.rightPivot.2 =
      .both :=
  rfl

@[simp] theorem profiledRawJointCommonActualDirection_leftPivot_row
    (actual : ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    (profiledRawJointCommonActualDirection actual).direction.leftPivot.2 =
      .both :=
  rfl

end

/-! ## Tagged source-free finite data -/

/-- The common and recurrent modes use the same finite incidence payload but
must remain distinguishable by the total source-free transition. -/
inductive ProfiledRawJointHybridCode where
  | common (code : ProfiledRawJointIncidenceCode A (I := Unit))
  | oneSided (code : ProfiledRawJointIncidenceCode A (I := Unit))
  | dead
  deriving Fintype

/-- A live node exposes the original raw joint move; the dead completion has
no raw move. -/
abbrev ProfiledRawJointHybridMove :=
  Option (ProfiledRawJointLambdaFamilyMove A (I := Unit))

/-- Mode-aware source-free validity. -/
def ProfiledRawJointHybridMoveValid
    (code : ProfiledRawJointHybridCode A)
    (move : ProfiledRawJointHybridMove A) : Prop :=
  match code, move with
  | .common code, some move =>
      ProfiledRawJointIncidenceMoveValid A code move
  | .oneSided code, some move =>
      ProfiledRawJointIncidenceMoveValid A code move
  | .dead, none => True
  | _, _ => False

/-- Total finite successor.  A common node may stay common or exit once;
after exit, another simultaneous constructor is outside the real branch
shape and enters the dead completion. -/
noncomputable def profiledRawJointHybridNext
    (code : ProfiledRawJointHybridCode A)
    (move : ProfiledRawJointHybridMove A)
    (direction : ProfiledRawJointHybridDirection
      (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointHybridCode A :=
  match code, move, direction with
  | .common code, some move, .simultaneous input =>
      .common (profiledRawJointIncidenceNext A code.family move
        (profiledRawJointBothRestartDirection input))
  | .common code, some move, .strict actual =>
      .oneSided (profiledRawJointOneSidedNext A code move
        (profiledRawJointCommonActualDirection actual))
  | .oneSided code, some move, .strict actual =>
      .oneSided (profiledRawJointOneSidedNext A code move actual)
  | _, _, _ => .dead

/-! ## Literal hybrid semantics -/

/-- Exact semantic states of the common-prefix/recurrent unfolding. -/
inductive ProfiledRawJointHybridSemanticState
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂) where
  | common (world : ProfiledRawJointCommonBaseWorld A strategy)
  | oneSided (state :
      ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
  | dead

/-- Strict exit from one common world into the recursively exact one-sided
semantic state. -/
def profiledRawJointCommonExitState
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (world : ProfiledRawJointCommonBaseWorld A strategy)
    (actual : ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointOneSidedSemanticState A strategy (I := Unit) :=
  let family := profiledRawJointCommonWorldFamily A world
  let actual := profiledRawJointCommonActualDirection actual
  match actual.side with
  | .right =>
      { family := family.rightActualChild A actual.direction
        exactFibre := family.rightActualChild_exactFibreAt A actual.direction }
  | .left =>
      { family := family.leftActualChild A actual.direction
        exactFibre := family.leftActualChild_exactFibreAt A actual.direction }

/-- Literal total semantic step. -/
def ProfiledRawJointHybridSemanticState.step
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (state : ProfiledRawJointHybridSemanticState A strategy)
    (direction : ProfiledRawJointHybridDirection
      (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointHybridSemanticState A strategy :=
  match state, direction with
  | .common world, .simultaneous input =>
      .common (profiledRawJointCommonWorldAfterBoth A world input)
  | .common world, .strict actual =>
      .oneSided (profiledRawJointCommonExitState A world actual)
  | .oneSided state, .strict actual => .oneSided (state.step A actual)
  | _, _ => .dead

/-- Exact tagged finite erasure. -/
noncomputable def ProfiledRawJointHybridSemanticState.code
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (state : ProfiledRawJointHybridSemanticState A strategy) :
    ProfiledRawJointHybridCode A :=
  match state with
  | .common world =>
      .common ((profiledRawJointCommonWorldFamily A world).incidenceCode A)
  | .oneSided state => .oneSided (state.code A)
  | .dead => .dead

/-- Raw move of a live semantic node. -/
def ProfiledRawJointHybridSemanticState.move
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (state : ProfiledRawJointHybridSemanticState A strategy) :
    ProfiledRawJointHybridMove A :=
  match state with
  | .common world => some ((profiledRawJointCommonWorldFamily A world).move A)
  | .oneSided state => some (state.move A)
  | .dead => none

/-! ## Exact finite erasure -/

section
omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂]

/-- Finite code of the strict exit from a common world. -/
theorem profiledRawJointCommonExitState_code
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (world : ProfiledRawJointCommonBaseWorld A strategy)
    (actual : ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    (profiledRawJointCommonExitState A world actual).code A =
      profiledRawJointOneSidedNext A
        ((profiledRawJointCommonWorldFamily A world).incidenceCode A)
        ((profiledRawJointCommonWorldFamily A world).move A)
        (profiledRawJointCommonActualDirection actual) := by
  classical
  let normalized := profiledRawJointCommonActualDirection actual
  let family := profiledRawJointCommonWorldFamily A world
  let common := Classical.choice
    (nonempty_profiledRawJointCommonWorldSource_of_bothPivots A world
      normalized.direction (by rfl) (by rfl))
  cases hside : actual.side with
  | right =>
      simpa [profiledRawJointCommonExitState,
        profiledRawJointCommonActualDirection,
        ProfiledRawJointOneSidedSemanticState.code,
        profiledRawJointOneSidedNext, normalized, family, hside] using
        family.rightActualChild_incidenceCode_eq A normalized.direction common
  | left =>
      simpa [profiledRawJointCommonExitState,
        profiledRawJointCommonActualDirection,
        ProfiledRawJointOneSidedSemanticState.code,
        profiledRawJointOneSidedNext, normalized, family, hside] using
        family.leftActualChild_incidenceCode_eq A normalized.direction common

/-- The hybrid semantic step satisfies one source-free finite T1 equation in
all modes, including the total dead completion. -/
theorem ProfiledRawJointHybridSemanticState.step_code
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (state : ProfiledRawJointHybridSemanticState A strategy)
    (direction : ProfiledRawJointHybridDirection
      (In₁ := In₁) (In₂ := In₂)) :
    (state.step A direction).code A =
      profiledRawJointHybridNext A (state.code A) (state.move A) direction := by
  cases state with
  | common world =>
      cases direction with
      | simultaneous input =>
          simp only [ProfiledRawJointHybridSemanticState.step,
            ProfiledRawJointHybridSemanticState.code,
            ProfiledRawJointHybridSemanticState.move,
            profiledRawJointHybridNext]
          exact congrArg ProfiledRawJointHybridCode.common
            (profiledRawJointCommonWorldAfterBoth_incidenceCode A world input)
      | strict actual =>
          simp only [ProfiledRawJointHybridSemanticState.step,
            ProfiledRawJointHybridSemanticState.code,
            ProfiledRawJointHybridSemanticState.move,
            profiledRawJointHybridNext]
          exact congrArg ProfiledRawJointHybridCode.oneSided
            (profiledRawJointCommonExitState_code A world actual)
  | oneSided state =>
      cases direction with
      | simultaneous input => rfl
      | strict actual =>
          simp only [ProfiledRawJointHybridSemanticState.step,
            ProfiledRawJointHybridSemanticState.code,
            ProfiledRawJointHybridSemanticState.move,
            profiledRawJointHybridNext]
          congr 1
          exact state.step_code A actual
  | dead => rfl

/-- Every literal node exposes a valid tagged move. -/
theorem ProfiledRawJointHybridSemanticState.move_valid_of_winning
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (state : ProfiledRawJointHybridSemanticState A strategy) :
    ProfiledRawJointHybridMoveValid A (state.code A) (state.move A) := by
  cases state with
  | common world =>
      simpa [ProfiledRawJointHybridSemanticState.code,
        ProfiledRawJointHybridSemanticState.move,
        ProfiledRawJointHybridMoveValid,
        ProfiledRawJointSemanticFamily.incidenceCode] using
        (profiledRawJointCommonWorldFamily A world).move_valid_of_winning A hwin
  | oneSided state =>
      simpa [ProfiledRawJointHybridSemanticState.code,
        ProfiledRawJointHybridSemanticState.move,
        ProfiledRawJointHybridMoveValid,
        ProfiledRawJointOneSidedSemanticState.code] using
        state.move_valid_of_winning A hwin
  | dead => trivial

end

/-! ## Source-free semantic tree -/

/-- The full exact hybrid unfolding from one common world. -/
def profiledRawJointHybridSemanticTree
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :
    SourceFreeBeliefSemanticTree
      (ProfiledRawJointHybridDirection (In₁ := In₁) (In₂ := In₂))
      (ProfiledRawJointHybridMove A)
      (ProfiledRawJointHybridCode A) where
  Semantic := ProfiledRawJointHybridSemanticState A strategy
  initial := .common initial
  step := ProfiledRawJointHybridSemanticState.step A
  code := ProfiledRawJointHybridSemanticState.code A
  move := ProfiledRawJointHybridSemanticState.move A

section
omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂]

@[simp] theorem profiledRawJointHybridSemanticTree_initial_code
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :
    let raw := profiledRawJointHybridSemanticTree A initial
    raw.code raw.initial =
      .common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A) :=
  rfl

/-- T1 throughout the hybrid unfolding. -/
theorem profiledRawJointHybridSemanticTree_next_code
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (node : TreeNode (ProfiledRawJointHybridDirection
      (In₁ := In₁) (In₂ := In₂)))
    (direction : ProfiledRawJointHybridDirection
      (In₁ := In₁) (In₂ := In₂)) :
    let raw := profiledRawJointHybridSemanticTree A initial
    raw.code (raw.step (raw.stateAt node) direction) =
      profiledRawJointHybridNext A
        (raw.code (raw.stateAt node)) (raw.move (raw.stateAt node)) direction :=
  ProfiledRawJointHybridSemanticState.step_code A _ direction

/-- Node-local validity throughout the hybrid unfolding. -/
theorem profiledRawJointHybridSemanticTree_valid
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (node : TreeNode (ProfiledRawJointHybridDirection
      (In₁ := In₁) (In₂ := In₂))) :
    let raw := profiledRawJointHybridSemanticTree A initial
    ProfiledRawJointHybridMoveValid A
      (raw.code (raw.stateAt node)) (raw.move (raw.stateAt node)) :=
  ProfiledRawJointHybridSemanticState.move_valid_of_winning A hwin _

end

end

end DetParityAutomaton

end DistributedSynthesis
