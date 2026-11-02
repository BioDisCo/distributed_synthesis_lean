/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointCommonBaseWorld
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedActualChild
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenRawInitialOutputCoherence

/-!
# Local representation by a one-sided actual world

The proof-side choice of a right or left actual semantic child must not become
an observation of either process.  This file isolates the model fact that
makes that possible.

First, a finite local event records exactly what one process observes in one
environment round.  Equal local events, played from one generated base,
produce generated histories with equal local views and hence equal strategy
outputs.  The four concrete corollaries are precisely the two blind cases and
the two receive cases used by the dependent belief recurrence.

Second, the one-sided semantic children inherit the corresponding four
initial-output laws.  A left actual child contains only process-one entries,
so it supplies the process-one blind/right-block law and the process-two
right-receive law.  A right actual child supplies their mirror.  Fresh-child
provenance is used only in these proofs; no graph orientation, active side, or
strict-leader flag is exposed to a process.
-/

namespace DistributedSynthesis

universe i u v x y s

namespace DetParityAutomaton

variable {I : Type i}
variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}

noncomputable section

/-! ## The exact process-local event -/

/-- The information delivered to one process by one environment round.  A
blind event contains only the process's own input.  A receive event contains
both inputs; the two graph values that deliver a message are intentionally
identified. -/
def ProfiledRawJointLocalEventType
    (In₁ : Type u) (In₂ : Type v) : Proc → Type (max u v)
  | .one => In₁ ⊕ (In₁ × In₂)
  | .two => In₂ ⊕ (In₂ × In₁)

/-- Extract the exact local event.  In particular, process one maps `left`
and `both` to the same receive event, while process two maps `right` and
`both` to the same receive event. -/
def profiledRawJointLocalEvent
    (d : Proc) (round : EnvironmentRound In₁ In₂) :
    ProfiledRawJointLocalEventType In₁ In₂ d :=
  match d with
  | .one =>
      match round.graph with
      | .right => Sum.inl round.inputOne
      | .left | .both => Sum.inr (round.inputOne, round.inputTwo)
  | .two =>
      match round.graph with
      | .left => Sum.inl round.inputTwo
      | .right | .both => Sum.inr (round.inputTwo, round.inputOne)

/-- Two rounds are locally compatible for a process exactly when they expose
the same process-local event. -/
def ProfiledRawJointLocalRoundCompatible
    (d : Proc) (actual represented : EnvironmentRound In₁ In₂) : Prop :=
  profiledRawJointLocalEvent d actual =
    profiledRawJointLocalEvent d represented

/-- Local compatibility is exactly enough to preserve the next local view
when both rounds start at the same concrete history. -/
theorem nextView_eq_of_profiledRawJointLocalRoundCompatible
    (d : Proc) (base : History In₁ In₂ Graph Out₁ Out₂)
    (actual represented : EnvironmentRound In₁ In₂)
    (hcompatible :
      ProfiledRawJointLocalRoundCompatible d actual represented) :
    nextView d base actual = nextView d base represented := by
  rcases actual with ⟨actualOne, actualTwo, actualGraph⟩
  rcases represented with
    ⟨representedOne, representedTwo, representedGraph⟩
  cases d <;> cases actualGraph <;> cases representedGraph <;>
    simp [ProfiledRawJointLocalRoundCompatible,
      profiledRawJointLocalEvent, nextView, advanceViewsWithEnvironment]
      at hcompatible ⊢
  all_goals
    first
    | exact Sum.inl.inj hcompatible
    | exact ⟨congrArg Prod.fst (Sum.inr.inj hcompatible),
        congrArg Prod.snd (Sum.inr.inj hcompatible)⟩

/-! ## Exact generated-world representation -/

/-- One proof-side concrete world represents another for process `d` when
both are genuine histories of the same strategy and their exact current local
views agree.  The relation contains no finite-code or orientation field. -/
structure ProfiledRawJointLocalWorldRepresents
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂) (d : Proc)
    (actual represented : History In₁ In₂ Graph Out₁ Out₂) : Prop where
  actual_generated : StrategyGeneratedPrefix strategy actual
  represented_generated : StrategyGeneratedPrefix strategy represented
  view_eq : currentView d actual = currentView d represented

/-- Equal represented process-one views force equal literal strategy
outputs. -/
theorem ProfiledRawJointLocalWorldRepresents.outputOne_eq
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {actual represented : History In₁ In₂ Graph Out₁ Out₂}
    (hrep : ProfiledRawJointLocalWorldRepresents strategy Proc.one
      actual represented) :
    strategy.one (currentView Proc.one actual) =
      strategy.one (currentView Proc.one represented) :=
  congrArg strategy.one hrep.view_eq

/-- Process-two output mirror. -/
theorem ProfiledRawJointLocalWorldRepresents.outputTwo_eq
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {actual represented : History In₁ In₂ Graph Out₁ Out₂}
    (hrep : ProfiledRawJointLocalWorldRepresents strategy Proc.two
      actual represented) :
    strategy.two (currentView Proc.two actual) =
      strategy.two (currentView Proc.two represented) :=
  congrArg strategy.two hrep.view_eq

/-- The central one-step representation lemma.  The actual and represented
rounds are both appended to one generated base; local-event equality is the
only observational hypothesis. -/
theorem oneSidedActualWorld_step_represents
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (base : History In₁ In₂ Graph Out₁ Out₂)
    (hbase : StrategyGeneratedPrefix strategy base)
    (d : Proc) (actual represented : EnvironmentRound In₁ In₂)
    (hcompatible :
      ProfiledRawJointLocalRoundCompatible d actual represented) :
    ProfiledRawJointLocalWorldRepresents strategy d
      (History.append base (nextRound strategy base actual))
      (History.append base (nextRound strategy base represented)) where
  actual_generated := StrategyGeneratedPrefix.append hbase actual
  represented_generated := StrategyGeneratedPrefix.append hbase represented
  view_eq := by
    rw [currentView_append_nextRound, currentView_append_nextRound]
    exact nextView_eq_of_profiledRawJointLocalRoundCompatible d base actual
      represented hcompatible

/-! ## Common-base operations -/

variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

variable [Fintype I]
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

/-- Change only the process-one input of a proof-side common-base world. -/
def ProfiledRawJointCommonBaseWorld.withInputOne
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (world : ProfiledRawJointCommonBaseWorld A strategy)
    (inputOne : In₁) : ProfiledRawJointCommonBaseWorld A strategy :=
  { world with inputOne := inputOne }

/-- Change only the process-two input. -/
def ProfiledRawJointCommonBaseWorld.withInputTwo
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (world : ProfiledRawJointCommonBaseWorld A strategy)
    (inputTwo : In₂) : ProfiledRawJointCommonBaseWorld A strategy :=
  { world with inputTwo := inputTwo }

/-- Literal one-round history of a common-base world at a selected graph. -/
def ProfiledRawJointCommonBaseWorld.history
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (world : ProfiledRawJointCommonBaseWorld A strategy) (graph : Graph) :
    History In₁ In₂ Graph Out₁ Out₂ :=
  History.append world.base
    (nextRound strategy world.base
      ⟨world.inputOne, world.inputTwo, graph⟩)

theorem ProfiledRawJointCommonBaseWorld.history_generated
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (world : ProfiledRawJointCommonBaseWorld A strategy) (graph : Graph) :
    StrategyGeneratedPrefix strategy (world.history A graph) :=
  StrategyGeneratedPrefix.append world.base_generated _

/-! ## The four raw local-step laws -/

/-- Process one is blind in a strict-right round.  The actual process-two
child world therefore represents every hidden process-two input. -/
theorem ProfiledRawJointCommonBaseWorld.noRecvOne_step_represents
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (world : ProfiledRawJointCommonBaseWorld A strategy)
    (hiddenInputTwo : In₂) :
    ProfiledRawJointLocalWorldRepresents strategy Proc.one
      (world.procTwo A).rightHistory
      ((world.withInputTwo A hiddenInputTwo).procTwo A).rightHistory := by
  simpa [ProfiledRawJointCommonBaseWorld.procTwo,
    ProfiledRawJointCommonBaseWorld.withInputTwo, procTwoFreshPair] using
    (oneSidedActualWorld_step_represents strategy world.base
      world.base_generated Proc.one
      ⟨world.inputOne, world.inputTwo, Graph.right⟩
      ⟨world.inputOne, hiddenInputTwo, Graph.right⟩ (by
        simp [ProfiledRawJointLocalRoundCompatible,
          profiledRawJointLocalEvent]))

/-- Process-two blind-step mirror for a strict-left round. -/
theorem ProfiledRawJointCommonBaseWorld.noRecvTwo_step_represents
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (world : ProfiledRawJointCommonBaseWorld A strategy)
    (hiddenInputOne : In₁) :
    ProfiledRawJointLocalWorldRepresents strategy Proc.two
      (world.procOne A).leftHistory
      ((world.withInputOne A hiddenInputOne).procOne A).leftHistory := by
  simpa [ProfiledRawJointCommonBaseWorld.procOne,
    ProfiledRawJointCommonBaseWorld.withInputOne, procOneFreshPair] using
    (oneSidedActualWorld_step_represents strategy world.base
      world.base_generated Proc.two
      ⟨world.inputOne, world.inputTwo, Graph.left⟩
      ⟨hiddenInputOne, world.inputTwo, Graph.left⟩ (by
        simp [ProfiledRawJointLocalRoundCompatible,
          profiledRawJointLocalEvent]))

/-- Process one cannot distinguish the two receive graphs `left` and `both`.
Both histories remain literal generated worlds of the same one-sided
process-one child. -/
theorem ProfiledRawJointCommonBaseWorld.recvOne_step_represents
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (world : ProfiledRawJointCommonBaseWorld A strategy)
    (actualGraph compatibleGraph : Graph)
    (hactual : actualGraph = .left ∨ actualGraph = .both)
    (hcompatible : compatibleGraph = .left ∨ compatibleGraph = .both) :
    ProfiledRawJointLocalWorldRepresents strategy Proc.one
      (world.history A actualGraph) (world.history A compatibleGraph) := by
  apply oneSidedActualWorld_step_represents strategy world.base
    world.base_generated Proc.one
  rcases hactual with rfl | rfl <;> rcases hcompatible with rfl | rfl <;>
    simp [ProfiledRawJointLocalRoundCompatible,
      profiledRawJointLocalEvent]

/-- Process-two receive mirror: `right` and `both` are one local event. -/
theorem ProfiledRawJointCommonBaseWorld.recvTwo_step_represents
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (world : ProfiledRawJointCommonBaseWorld A strategy)
    (actualGraph compatibleGraph : Graph)
    (hactual : actualGraph = .right ∨ actualGraph = .both)
    (hcompatible : compatibleGraph = .right ∨ compatibleGraph = .both) :
    ProfiledRawJointLocalWorldRepresents strategy Proc.two
      (world.history A actualGraph) (world.history A compatibleGraph) := by
  apply oneSidedActualWorld_step_represents strategy world.base
    world.base_generated Proc.two
  rcases hactual with rfl | rfl <;> rcases hcompatible with rfl | rfl <;>
    simp [ProfiledRawJointLocalRoundCompatible,
      profiledRawJointLocalEvent]

/-! ## Four recursive initial-output laws -/

/-- The process-one blind initial output is constant across one left actual
child.  This is the raw law consumed by `noRecvOne`. -/
theorem ProfiledRawJointSemanticFamily.leftActualChild_noRecvOne_initialOutput_eq
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := I))
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (leftIndex rightIndex : I)
    (leftChild rightChild : ProcOnePairedEntryRep strategy × A.State)
    (hleft : (family.leftActualChild A direction).right leftIndex =
      some leftChild)
    (hright : (family.leftActualChild A direction).right rightIndex =
      some rightChild)
    (inputOne : In₁) :
    leftChild.1.lambdaOfStrategy.blind [] inputOne =
      rightChild.1.lambdaOfStrategy.blind [] inputOne := by
  exact procOnePairedEntry_blindInitialOutput_eq_of_view_eq leftChild.1
    rightChild.1
      (family.leftSelectedChild_view_shared A direction leftIndex rightIndex
        leftChild rightChild hleft hright) inputOne

/-- The process-two blind mirror on a right actual child. -/
theorem ProfiledRawJointSemanticFamily.rightActualChild_noRecvTwo_initialOutput_eq
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := I))
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (leftIndex rightIndex : I)
    (leftChild rightChild : ProcTwoPairedEntryRep strategy × A.State)
    (hleft : (family.rightActualChild A direction).left leftIndex =
      some leftChild)
    (hright : (family.rightActualChild A direction).left rightIndex =
      some rightChild)
    (inputTwo : In₂) :
    leftChild.1.lambdaOfStrategy.blind [] inputTwo =
      rightChild.1.lambdaOfStrategy.blind [] inputTwo := by
  exact procTwoPairedEntry_blindInitialOutput_eq_of_view_eq leftChild.1
    rightChild.1
      (family.rightSelectedChild_view_shared A direction leftIndex rightIndex
        leftChild rightChild hleft hright) inputTwo

/-- The process-one receive initial output is constant across a right actual
child, for either physical row.  This is the raw `recvOne` law. -/
theorem ProfiledRawJointSemanticFamily.rightActualChild_recvOne_initialOutput_eq
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := I))
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (leftIndex rightIndex : I)
    (leftChild rightChild : ProcTwoPairedEntryRep strategy × A.State)
    (hleft : (family.rightActualChild A direction).left leftIndex =
      some leftChild)
    (hright : (family.rightActualChild A direction).left rightIndex =
      some rightChild)
    (row : PairedEntryRow) (inputOne : In₁) (inputTwo : In₂) :
    pairedLeftInformedForRow row
        (profiledLeftReceiverStrategy A leftChild.1.code
          leftChild.1.lambdaOfStrategy [] (inputOne, inputTwo)).physical =
      pairedLeftInformedForRow row
        (profiledLeftReceiverStrategy A rightChild.1.code
          rightChild.1.lambdaOfStrategy [] (inputOne, inputTwo)).physical := by
  rcases family.rightSelectedChild_eq_some_source A direction leftIndex
      leftChild hleft with
    ⟨leftMember, leftRow, _hleftMember, _hleftPattern, rfl⟩
  rcases family.rightSelectedChild_eq_some_source A direction rightIndex
      rightChild hright with
    ⟨rightMember, rightRow, _hrightMember, _hrightPattern, rfl⟩
  exact procTwoPairedEntry_leftReceiveInitialOutput_eq_of_fresh_view_eq A
    _ _
    ({ Index := Unit
       entry := fun _ => leftMember.1
       past := direction.rightPhysicalPast
       input := direction.rightInput
       candidate := ((), leftRow)
       child_eq := rfl } : ProcTwoViewClassChildProvenance strategy _)
    ({ Index := Unit
       entry := fun _ => rightMember.1
       past := direction.rightPhysicalPast
       input := direction.rightInput
       candidate := ((), rightRow)
       child_eq := rfl } : ProcTwoViewClassChildProvenance strategy _)
    (family.rightSelectedChild_view_shared A direction leftIndex rightIndex
      _ _ hleft hright) row inputOne inputTwo

/-- Process-two receive mirror on a left actual child. -/
theorem ProfiledRawJointSemanticFamily.leftActualChild_recvTwo_initialOutput_eq
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (family : ProfiledRawJointSemanticFamily A strategy (I := I))
    (direction : ProfiledRawJointFamilyDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (leftIndex rightIndex : I)
    (leftChild rightChild : ProcOnePairedEntryRep strategy × A.State)
    (hleft : (family.leftActualChild A direction).right leftIndex =
      some leftChild)
    (hright : (family.leftActualChild A direction).right rightIndex =
      some rightChild)
    (row : PairedEntryRow) (inputOne : In₁) (inputTwo : In₂) :
    pairedRightInformedForRow row
        (profiledRightReceiverStrategy A leftChild.1.code
          leftChild.1.lambdaOfStrategy [] (inputTwo, inputOne)).physical =
      pairedRightInformedForRow row
        (profiledRightReceiverStrategy A rightChild.1.code
          rightChild.1.lambdaOfStrategy [] (inputTwo, inputOne)).physical := by
  rcases family.leftSelectedChild_eq_some_source A direction leftIndex
      leftChild hleft with
    ⟨leftMember, leftRow, _hleftMember, _hleftPattern, rfl⟩
  rcases family.leftSelectedChild_eq_some_source A direction rightIndex
      rightChild hright with
    ⟨rightMember, rightRow, _hrightMember, _hrightPattern, rfl⟩
  exact procOnePairedEntry_rightReceiveInitialOutput_eq_of_fresh_view_eq A
    _ _
    ({ Index := Unit
       entry := fun _ => leftMember.1
       past := direction.leftPhysicalPast
       input := direction.leftInput
       candidate := ((), leftRow)
       child_eq := rfl } : ProcOneViewClassChildProvenance strategy _)
    ({ Index := Unit
       entry := fun _ => rightMember.1
       past := direction.leftPhysicalPast
       input := direction.leftInput
       candidate := ((), rightRow)
       child_eq := rfl } : ProcOneViewClassChildProvenance strategy _)
    (family.leftSelectedChild_view_shared A direction leftIndex rightIndex
      _ _ hleft hright) row inputOne inputTwo

end

end DetParityAutomaton

end DistributedSynthesis
