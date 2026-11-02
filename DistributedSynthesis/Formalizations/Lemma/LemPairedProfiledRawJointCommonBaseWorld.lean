/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointSemanticChild

/-!
# A single common-base semantic world

A recursively meaningful raw world is not the product of two independently
extended histories.  The minimal semantic carrier is one generated base,
one pair of current closing inputs, and one carried automaton root.  Its two
orientation projections are the literal `procOneFreshPair` and
`procTwoFreshPair` built from that same base.

For a right block the existing raw lambda computes the process-two slot, and
for a left block it computes the process-one slot.  The opposite projection
is not another application of that lambda.  Once the actual slot is known,
the exact missing finite data are only

* after a right block: the process-one projection's `left` state and its
  right initial-action profile;
* after a left block: the process-two projection's `right` state and its
  left initial-action profile.

The common `both` state and carried root are already present in the actual
slot.  The reconstruction lemmas below make this field audit exact.  Since a
raw move is chosen before the direction, the final payload interface is a
function of the selected row, physical past, and closing input; it is still
proof-side move data, not a process-visible orientation or leader bit.
-/

namespace DistributedSynthesis

universe i u v x y s

namespace DetParityAutomaton

variable {I : Type i}
variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Fintype I]
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]

/-! ## The semantic world and its two literal projections -/

/-- One actual semantic world at a pending graph choice.  The root is the
single block-minimum/root payload carried by both orientation projections. -/
structure ProfiledRawJointCommonBaseWorld
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂) where
  base : History In₁ In₂ Graph Out₁ Out₂
  base_generated : StrategyGeneratedPrefix strategy base
  inputOne : In₁
  inputTwo : In₂
  root : A.State

/-- Process-one `left`/`both` projection, definitionally a fresh pair at the
world's one generated base. -/
def ProfiledRawJointCommonBaseWorld.procOne
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (world : ProfiledRawJointCommonBaseWorld A strategy) :
    ProcOnePairedEntryRep strategy :=
  procOneFreshPair strategy world.base world.base_generated world.inputOne
    world.inputTwo

/-- Process-two `right`/`both` projection from the same base. -/
def ProfiledRawJointCommonBaseWorld.procTwo
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (world : ProfiledRawJointCommonBaseWorld A strategy) :
    ProcTwoPairedEntryRep strategy :=
  procTwoFreshPair strategy world.base world.base_generated world.inputOne
    world.inputTwo

/-- Process-one projection with the common carried root. -/
def ProfiledRawJointCommonBaseWorld.procOneMember
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (world : ProfiledRawJointCommonBaseWorld A strategy) :
    ProcOnePairedEntryRep strategy × A.State :=
  (world.procOne A, world.root)

/-- Process-two projection with the same root. -/
def ProfiledRawJointCommonBaseWorld.procTwoMember
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (world : ProfiledRawJointCommonBaseWorld A strategy) :
    ProcTwoPairedEntryRep strategy × A.State :=
  (world.procTwo A, world.root)

/-- Complete finite process-one/right slot of the world. -/
def ProfiledRawJointCommonBaseWorld.procOneSlot
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (world : ProfiledRawJointCommonBaseWorld A strategy) :
    ProfiledRawRightSlot A :=
  profiledRawRightSlotOfSemanticPair A (world.procOneMember A)

/-- Complete finite process-two/left slot of the world. -/
def ProfiledRawJointCommonBaseWorld.procTwoSlot
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (world : ProfiledRawJointCommonBaseWorld A strategy) :
    ProfiledRawLeftSlot A :=
  profiledRawLeftSlotOfSemanticPair A (world.procTwoMember A)

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂]

@[simp] theorem ProfiledRawJointCommonBaseWorld.procOne_leftHistory
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (world : ProfiledRawJointCommonBaseWorld A strategy) :
    (world.procOne A).leftHistory =
      History.append world.base
        (nextRound strategy world.base
          ⟨world.inputOne, world.inputTwo, Graph.left⟩) := rfl

@[simp] theorem ProfiledRawJointCommonBaseWorld.procOne_bothHistory
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (world : ProfiledRawJointCommonBaseWorld A strategy) :
    (world.procOne A).bothHistory =
      History.append world.base
        (nextRound strategy world.base
          ⟨world.inputOne, world.inputTwo, Graph.both⟩) := rfl

@[simp] theorem ProfiledRawJointCommonBaseWorld.procTwo_rightHistory
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (world : ProfiledRawJointCommonBaseWorld A strategy) :
    (world.procTwo A).rightHistory =
      History.append world.base
        (nextRound strategy world.base
          ⟨world.inputOne, world.inputTwo, Graph.right⟩) := rfl

@[simp] theorem ProfiledRawJointCommonBaseWorld.procTwo_bothHistory
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (world : ProfiledRawJointCommonBaseWorld A strategy) :
    (world.procTwo A).bothHistory =
      History.append world.base
        (nextRound strategy world.base
          ⟨world.inputOne, world.inputTwo, Graph.both⟩) := rfl

/-- The two projections overlap at the literal `both` history, not merely at
equal local views or equal finite codes. -/
@[simp] theorem ProfiledRawJointCommonBaseWorld.procOne_bothHistory_eq_procTwo
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (world : ProfiledRawJointCommonBaseWorld A strategy) :
    (world.procOne A).bothHistory = (world.procTwo A).bothHistory := rfl

/-- Consequently the two finite entry codes share their `both` state. -/
@[simp] theorem ProfiledRawJointCommonBaseWorld.procOne_code_both_eq_procTwo
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (world : ProfiledRawJointCommonBaseWorld A strategy) :
    ((world.procOne A).code (A := A)).2 =
      ((world.procTwo A).code (A := A)).2 := rfl

end

/-! ## One-sided raw steps land in a common-base world -/

/-- Common-base world reached from one selected process-one row by a right
block.  The base stops immediately before the closing `right`/`both` choice. -/
def profiledRawRightCommonBaseWorld
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (member : ProcOnePairedEntryRep strategy × A.State)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (input : In₂ × In₁) : ProfiledRawJointCommonBaseWorld A strategy where
  base := extendPrefix strategy (profiledRawProcOneRowHistory member.1 row)
    (past.map rightEnvironment)
  base_generated := strategyGenerated_extendPrefix_basic strategy
    (profiledRawProcOneRowHistory_generated member.1 row) _
  inputOne := input.2
  inputTwo := input.1
  root := match row with
    | .first => blockMinState A member.1.code.1
        (member.1.lambdaOfStrategy.leftWord past)
    | .both => blockMinState A member.1.code.2
        (member.1.lambdaOfStrategy.bothWord past)

/-- Left-block mirror. -/
def profiledRawLeftCommonBaseWorld
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (member : ProcTwoPairedEntryRep strategy × A.State)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂) : ProfiledRawJointCommonBaseWorld A strategy where
  base := extendPrefix strategy (profiledRawProcTwoRowHistory member.1 row)
    (past.map leftEnvironment)
  base_generated := strategyGenerated_extendPrefix_basic strategy
    (profiledRawProcTwoRowHistory_generated member.1 row) _
  inputOne := input.1
  inputTwo := input.2
  root := match row with
    | .first => blockMinState A member.1.code.1
        (member.1.lambdaOfStrategy.rightWord past)
    | .both => blockMinState A member.1.code.2
        (member.1.lambdaOfStrategy.bothWord past)

omit [Inhabited In₁] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂]
    [Fintype Out₁] [Fintype Out₂] in
/-- The actual process-two child of a right raw step is definitionally the
process-two projection of its common-base world. -/
theorem profiledRawRightCommonBaseWorld_procTwoMember
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (member : ProcOnePairedEntryRep strategy × A.State)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (input : In₂ × In₁) :
    (profiledRawRightCommonBaseWorld A member row past input).procTwoMember A =
      profiledRawRightSemanticChildPair A member row past input := by
  cases row <;> rfl

omit [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂]
    [Fintype Out₁] [Fintype Out₂] in
/-- Actual process-one child mirror. -/
theorem profiledRawLeftCommonBaseWorld_procOneMember
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (member : ProcTwoPairedEntryRep strategy × A.State)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂) :
    (profiledRawLeftCommonBaseWorld A member row past input).procOneMember A =
      profiledRawLeftSemanticChildPair A member row past input := by
  cases row <;> rfl

omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] in
/-- Thus the existing right raw child computation gives exactly the actual
process-two slot of the common-base world. -/
theorem profiledRawRightCommonBaseWorld_procTwoSlot_eq
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (member : ProcOnePairedEntryRep strategy × A.State)
    (row : PairedEntryRow)
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    (profiledRawRightCommonBaseWorld A member row
        direction.rightPhysicalPast direction.rightInput).procTwoSlot A =
      profiledRawRightChildSlot A
        ((member.1.code, member.2),
          rightInitialFirstProfile member.1.lambdaOfStrategy)
        member.1.lambdaOfStrategy row direction.rightPhysicalPast
          direction.rightInput := by
  rw [ProfiledRawJointCommonBaseWorld.procTwoSlot,
    profiledRawRightCommonBaseWorld_procTwoMember]
  exact (profiledRawRightChildSlot_eq_semanticChildPairCode A direction
    member row).symm

omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] in
/-- Left raw child computation mirror. -/
theorem profiledRawLeftCommonBaseWorld_procOneSlot_eq
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (member : ProcTwoPairedEntryRep strategy × A.State)
    (row : PairedEntryRow)
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    (profiledRawLeftCommonBaseWorld A member row
        direction.leftPhysicalPast direction.leftInput).procOneSlot A =
      profiledRawLeftChildSlot A
        ((member.1.code, member.2),
          leftInitialFirstProfile member.1.lambdaOfStrategy)
        member.1.lambdaOfStrategy row direction.leftPhysicalPast
          direction.leftInput := by
  rw [ProfiledRawJointCommonBaseWorld.procOneSlot,
    profiledRawLeftCommonBaseWorld_procOneMember]
  exact (profiledRawLeftChildSlot_eq_semanticChildPairCode A direction
    member row).symm

/-! ## Exact finite companion payload -/

/-- Missing data for the process-one companion of a right-block actual slot:
its `left` objective state and right initial-action profile. -/
abbrev ProfiledRawRightCompanionPayload :=
  A.State × RightInitialActionProfile
    (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂)

/-- Missing data for the process-two companion of a left-block actual slot. -/
abbrev ProfiledRawLeftCompanionPayload :=
  A.State × LeftInitialActionProfile
    (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)

/-- Reconstruct the process-one companion slot.  Its `both` state and root
are reused from the actual process-two slot. -/
def profiledRawRightCompanionSlot
    (actual : ProfiledRawLeftSlot A)
    (payload : ProfiledRawRightCompanionPayload A) :
    ProfiledRawRightSlot A :=
  (((payload.1, actual.1.1.2), actual.1.2), payload.2)

/-- Left-block mirror. -/
def profiledRawLeftCompanionSlot
    (actual : ProfiledRawRightSlot A)
    (payload : ProfiledRawLeftCompanionPayload A) :
    ProfiledRawLeftSlot A :=
  (((payload.1, actual.1.1.2), actual.1.2), payload.2)

/-- Semantic payload supplied by a common-base world after a right block. -/
def ProfiledRawJointCommonBaseWorld.rightCompanionPayload
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (world : ProfiledRawJointCommonBaseWorld A strategy) :
    ProfiledRawRightCompanionPayload A :=
  (((world.procOne A).code (A := A)).1,
    rightInitialFirstProfile (world.procOne A).lambdaOfStrategy)

/-- Semantic payload supplied after a left block. -/
def ProfiledRawJointCommonBaseWorld.leftCompanionPayload
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (world : ProfiledRawJointCommonBaseWorld A strategy) :
    ProfiledRawLeftCompanionPayload A :=
  (((world.procTwo A).code (A := A)).1,
    leftInitialFirstProfile (world.procTwo A).lambdaOfStrategy)

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] in
/-- The right companion payload is exactly sufficient to recover the complete
process-one slot from the actual process-two slot. -/
theorem ProfiledRawJointCommonBaseWorld.rightCompanionSlot_eq
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (world : ProfiledRawJointCommonBaseWorld A strategy) :
    profiledRawRightCompanionSlot A (world.procTwoSlot A)
        (world.rightCompanionPayload A) =
      world.procOneSlot A := by
  rfl

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] in
/-- Left companion reconstruction mirror. -/
theorem ProfiledRawJointCommonBaseWorld.leftCompanionSlot_eq
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (world : ProfiledRawJointCommonBaseWorld A strategy) :
    profiledRawLeftCompanionSlot A (world.procOneSlot A)
        (world.leftCompanionPayload A) =
      world.procTwoSlot A := by
  rfl

/-! ## Move-level shape forced by the quantifier order -/

/-- Extra raw move payload needed to announce both projections after either
one-sided block.  The move is selected before Nature supplies the row, past,
and closing input, hence all three remain arguments of the payload function.
Inactive source lineages carry `none`, exactly as for the existing lambdas. -/
structure ProfiledRawJointCommonBaseMovePayload where
  rightCompanion : I → Option
    (PairedEntryRow → List (In₂ × In₁) → In₂ × In₁ →
      ProfiledRawRightCompanionPayload A)
  leftCompanion : I → Option
    (PairedEntryRow → List (In₁ × In₂) → In₁ × In₂ →
      ProfiledRawLeftCompanionPayload A)

end

end DetParityAutomaton

end DistributedSynthesis
