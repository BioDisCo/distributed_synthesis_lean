/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteGlobalMealyEmissionLocalCongruence
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenLocalEventOutputPair

/-!
# The profiled physical emission satisfies the four local output laws

This file gives a finite proof-global source carrier for one physical
emission.  It retains both right and left shadow alternatives.  Each shadow
stores a public fixed value/query, a current descriptor, one erased dependent
evaluation, and its sticky entry row.

The two local relations retain exactly what the corresponding process needs:

* process one keeps the right public sender controller, and the left public
  receiver controller/current/sticky row;
* process two keeps the left public sender controller, and the right public
  receiver controller/current/sticky row.

Consequently the blind no-receive output laws are unconditional across the
hidden current, member, root, row, and partner input.  The receive laws use
the common delivered current and sticky row and then invoke the exact
dependent receiver pair.  Only preservation of these finite relations by the
model's source recurrence remains when constructing `MealyLocalCongruence`.
-/

namespace DistributedSynthesis

universe i u v w x y s

namespace DetParityAutomaton

variable {I : Type i}
variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Fintype I] [Inhabited I]
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

variable (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
variable (hwin : ∀ env : EnvironmentSequence In₁ In₂,
  A.Accepts (execution strategy env))
variable (basis : ∀ state : PairedProfiledTreeState A,
  (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
variable (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))

/-- Public right controller/query data. -/
abbrev ProfiledOpenRightEmissionPublic :=
  Σ value : ProfiledOpenFixedRightPinnedValue A initialCode,
    ProfiledOpenFixedRightPinnedBlockQuery.{i, u, v, x, y, s,
      max i u v x y s} A initialCode value

/-- Public left controller/query data. -/
abbrev ProfiledOpenLeftEmissionPublic :=
  Σ value : ProfiledOpenFixedLeftPinnedValue A initialCode,
    ProfiledOpenFixedLeftPinnedBlockQuery.{i, u, v, x, y, s,
      max i u v x y s} A initialCode value

/-- One finite right-shadow alternative. -/
structure ProfiledOpenRightEmissionAlternative where
  queryData : ProfiledOpenRightEmissionPublic A initialCode
  reachable : ProfiledOpenFixedRightQueryReachable A initialCode queryData.1
    queryData.2
  current : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I) initialCode
  evaluation : ProfiledOpenFixedRightReanchoredRowEvaluation A strategy hwin
    basis initialCode current queryData.1 queryData.2
  entryRow : PairedEntryRow

/-- One finite left-shadow alternative. -/
structure ProfiledOpenLeftEmissionAlternative where
  queryData : ProfiledOpenLeftEmissionPublic A initialCode
  reachable : ProfiledOpenFixedLeftQueryReachable A initialCode queryData.1
    queryData.2
  current : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I) initialCode
  evaluation : ProfiledOpenFixedLeftReanchoredRowEvaluation A strategy hwin
    basis initialCode current queryData.1 queryData.2
  entryRow : PairedEntryRow

/-- Both shadows are proof-global alternatives.  Runtime output selection
still uses only the two honest local receive events. -/
abbrev ProfiledOpenLocalEventEmissionState :=
  ProfiledOpenRightEmissionAlternative A strategy hwin basis initialCode ×
    ProfiledOpenLeftEmissionAlternative A strategy hwin basis initialCode

/-- Literal profiled physical Mealy emission. -/
noncomputable def profiledOpenLocalEventEmission
    (state : ProfiledOpenLocalEventEmissionState A strategy hwin basis
      initialCode)
    (round : EnvironmentRound In₁ In₂) : Out₁ × Out₂ :=
  let right := profiledOpenWitnessedRightRoundOverlayOfEvaluation A strategy
    hwin basis initialCode state.1.reachable state.1.evaluation
      state.1.entryRow
  let left := profiledOpenWitnessedLeftRoundOverlayOfEvaluation A strategy
    hwin basis initialCode state.2.reachable state.2.evaluation
      state.2.entryRow
  profiledOpenWitnessedOutputOfLocalEvents A initialCode right left
    (physicalReceivedOne round.graph) (physicalReceivedTwo round.graph)
    round.inputOne round.inputTwo

/-! ## The exact finite local relations -/

/-- The right blind behavior carried by one alternative. -/
noncomputable def profiledOpenRightEmissionSender
    (state : ProfiledOpenRightEmissionAlternative A strategy hwin basis
      initialCode) (inputOne : In₁) : Out₁ :=
  profiledOpenWitnessedRightSenderOutput A initialCode
    (profiledOpenWitnessedRightRoundOverlayOfEvaluation A strategy hwin basis
      initialCode state.reachable state.evaluation state.entryRow) inputOne

/-- The right informed behavior. -/
noncomputable def profiledOpenRightEmissionReceiver
    (state : ProfiledOpenRightEmissionAlternative A strategy hwin basis
      initialCode) (inputOne : In₁) (inputTwo : In₂) : Out₂ :=
  profiledOpenWitnessedRightReceiverOutput A initialCode
    (profiledOpenWitnessedRightRoundOverlayOfEvaluation A strategy hwin basis
      initialCode state.reachable state.evaluation state.entryRow)
    inputOne inputTwo

/-- The left blind behavior. -/
noncomputable def profiledOpenLeftEmissionSender
    (state : ProfiledOpenLeftEmissionAlternative A strategy hwin basis
      initialCode) (inputTwo : In₂) : Out₂ :=
  profiledOpenWitnessedLeftSenderOutput A initialCode
    (profiledOpenWitnessedLeftRoundOverlayOfEvaluation A strategy hwin basis
      initialCode state.reachable state.evaluation state.entryRow) inputTwo

/-- The left informed behavior. -/
noncomputable def profiledOpenLeftEmissionReceiver
    (state : ProfiledOpenLeftEmissionAlternative A strategy hwin basis
      initialCode) (inputOne : In₁) (inputTwo : In₂) : Out₁ :=
  profiledOpenWitnessedLeftReceiverOutput A initialCode
    (profiledOpenWitnessedLeftRoundOverlayOfEvaluation A strategy hwin basis
      initialCode state.reachable state.evaluation state.entryRow)
    inputOne inputTwo

/-- Process one retains exactly its right blind behavior and its left
informed behavior.  The common-data constructors below prove this relation
from cross-current sender homogeneity and same-current receiver homogeneity. -/
def ProfiledOpenLocalEventEqOne
    (left right : ProfiledOpenLocalEventEmissionState A strategy hwin basis
      initialCode) : Prop :=
  (∀ inputOne,
    profiledOpenRightEmissionSender A strategy hwin basis initialCode left.1
        inputOne =
      profiledOpenRightEmissionSender A strategy hwin basis initialCode right.1
        inputOne) ∧
    ∀ inputOne inputTwo,
      profiledOpenLeftEmissionReceiver A strategy hwin basis initialCode left.2
          inputOne inputTwo =
        profiledOpenLeftEmissionReceiver A strategy hwin basis initialCode
          right.2 inputOne inputTwo

/-- Process-two mirror. -/
def ProfiledOpenLocalEventEqTwo
    (left right : ProfiledOpenLocalEventEmissionState A strategy hwin basis
      initialCode) : Prop :=
  (∀ inputTwo,
    profiledOpenLeftEmissionSender A strategy hwin basis initialCode left.2
        inputTwo =
      profiledOpenLeftEmissionSender A strategy hwin basis initialCode right.2
        inputTwo) ∧
    ∀ inputOne inputTwo,
      profiledOpenRightEmissionReceiver A strategy hwin basis initialCode
          left.1 inputOne inputTwo =
        profiledOpenRightEmissionReceiver A strategy hwin basis initialCode
          right.1 inputOne inputTwo

omit [Inhabited I] [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenLocalEventEqOne_refl
    (state : ProfiledOpenLocalEventEmissionState A strategy hwin basis
      initialCode) :
    ProfiledOpenLocalEventEqOne A strategy hwin basis initialCode state state :=
  ⟨fun _ ↦ rfl, fun _ _ ↦ rfl⟩

omit [Inhabited I] [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenLocalEventEqTwo_refl
    (state : ProfiledOpenLocalEventEmissionState A strategy hwin basis
      initialCode) :
    ProfiledOpenLocalEventEqTwo A strategy hwin basis initialCode state state :=
  ⟨fun _ ↦ rfl, fun _ _ ↦ rfl⟩

/-! ## Semantic constructors for the local relations -/

/-- Package one right evaluation as an emission alternative. -/
def profiledOpenRightEmissionAlternativeOfEvaluation
    {current : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode}
    {value : ProfiledOpenFixedRightPinnedValue A initialCode}
    {query : ProfiledOpenFixedRightPinnedBlockQuery A initialCode value}
    (reachable : ProfiledOpenFixedRightQueryReachable A initialCode value
      query)
    (evaluation : ProfiledOpenFixedRightReanchoredRowEvaluation A strategy
      hwin basis initialCode current value query)
    (entryRow : PairedEntryRow) :
    ProfiledOpenRightEmissionAlternative A strategy hwin basis initialCode :=
  { queryData := ⟨value, query⟩
    reachable := reachable
    current := current
    evaluation := evaluation
    entryRow := entryRow }

/-- Left packaging mirror. -/
def profiledOpenLeftEmissionAlternativeOfEvaluation
    {current : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode}
    {value : ProfiledOpenFixedLeftPinnedValue A initialCode}
    {query : ProfiledOpenFixedLeftPinnedBlockQuery A initialCode value}
    (reachable : ProfiledOpenFixedLeftQueryReachable A initialCode value
      query)
    (evaluation : ProfiledOpenFixedLeftReanchoredRowEvaluation A strategy hwin
      basis initialCode current value query)
    (entryRow : PairedEntryRow) :
    ProfiledOpenLeftEmissionAlternative A strategy hwin basis initialCode :=
  { queryData := ⟨value, query⟩
    reachable := reachable
    current := current
    evaluation := evaluation
    entryRow := entryRow }

omit [Inhabited I] [Inhabited Out₁] [Inhabited Out₂] in
/-- The process-one relation is generated by exactly the asymmetric data
available after the local-event split: the right blind alternatives may have
different currents and rows, while the left receive alternatives share the
delivered current and sticky row. -/
theorem profiledOpenLocalEventEqOne_of_crossCurrent_right_of_sameCurrent_left
    {rightValue : ProfiledOpenFixedRightPinnedValue A initialCode}
    {rightQuery : ProfiledOpenFixedRightPinnedBlockQuery A initialCode
      rightValue}
    (rightReachable : ProfiledOpenFixedRightQueryReachable A initialCode
      rightValue rightQuery)
    {rightCurrent₁ rightCurrent₂ :
      ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I) initialCode}
    (rightEvaluation₁ : ProfiledOpenFixedRightReanchoredRowEvaluation A
      strategy hwin basis initialCode rightCurrent₁ rightValue rightQuery)
    (rightEvaluation₂ : ProfiledOpenFixedRightReanchoredRowEvaluation A
      strategy hwin basis initialCode rightCurrent₂ rightValue rightQuery)
    (rightRow₁ rightRow₂ : PairedEntryRow)
    {leftValue : ProfiledOpenFixedLeftPinnedValue A initialCode}
    {leftQuery : ProfiledOpenFixedLeftPinnedBlockQuery A initialCode leftValue}
    (leftReachable : ProfiledOpenFixedLeftQueryReachable A initialCode
      leftValue leftQuery)
    {leftCurrent : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode}
    (leftEvaluation₁ leftEvaluation₂ :
      ProfiledOpenFixedLeftReanchoredRowEvaluation A strategy hwin basis
        initialCode leftCurrent leftValue leftQuery)
    (leftRow : PairedEntryRow) :
    ProfiledOpenLocalEventEqOne A strategy hwin basis initialCode
      (profiledOpenRightEmissionAlternativeOfEvaluation A strategy hwin basis
          initialCode rightReachable rightEvaluation₁ rightRow₁,
        profiledOpenLeftEmissionAlternativeOfEvaluation A strategy hwin basis
          initialCode leftReachable leftEvaluation₁ leftRow)
      (profiledOpenRightEmissionAlternativeOfEvaluation A strategy hwin basis
          initialCode rightReachable rightEvaluation₂ rightRow₂,
        profiledOpenLeftEmissionAlternativeOfEvaluation A strategy hwin basis
          initialCode leftReachable leftEvaluation₂ leftRow) := by
  constructor
  · intro inputOne
    exact profiledOpenWitnessedRightSenderOutput_crossCurrent A strategy hwin
      basis initialCode rightReachable rightEvaluation₁ rightEvaluation₂
        rightRow₁ rightRow₂ inputOne
  · intro inputOne inputTwo
    exact profiledOpenWitnessedLeftReceiverOutput_sameCurrent A strategy hwin
      basis initialCode leftReachable leftEvaluation₁ leftEvaluation₂ leftRow
        inputOne inputTwo

omit [Inhabited I] [Inhabited Out₁] [Inhabited Out₂] in
/-- Process-two mirror: arbitrary left blind current, one delivered right
receiver current and sticky row. -/
theorem profiledOpenLocalEventEqTwo_of_crossCurrent_left_of_sameCurrent_right
    {leftValue : ProfiledOpenFixedLeftPinnedValue A initialCode}
    {leftQuery : ProfiledOpenFixedLeftPinnedBlockQuery A initialCode leftValue}
    (leftReachable : ProfiledOpenFixedLeftQueryReachable A initialCode
      leftValue leftQuery)
    {leftCurrent₁ leftCurrent₂ :
      ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I) initialCode}
    (leftEvaluation₁ : ProfiledOpenFixedLeftReanchoredRowEvaluation A strategy
      hwin basis initialCode leftCurrent₁ leftValue leftQuery)
    (leftEvaluation₂ : ProfiledOpenFixedLeftReanchoredRowEvaluation A strategy
      hwin basis initialCode leftCurrent₂ leftValue leftQuery)
    (leftRow₁ leftRow₂ : PairedEntryRow)
    {rightValue : ProfiledOpenFixedRightPinnedValue A initialCode}
    {rightQuery : ProfiledOpenFixedRightPinnedBlockQuery A initialCode
      rightValue}
    (rightReachable : ProfiledOpenFixedRightQueryReachable A initialCode
      rightValue rightQuery)
    {rightCurrent : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode}
    (rightEvaluation₁ rightEvaluation₂ :
      ProfiledOpenFixedRightReanchoredRowEvaluation A strategy hwin basis
        initialCode rightCurrent rightValue rightQuery)
    (rightRow : PairedEntryRow) :
    ProfiledOpenLocalEventEqTwo A strategy hwin basis initialCode
      (profiledOpenRightEmissionAlternativeOfEvaluation A strategy hwin basis
          initialCode rightReachable rightEvaluation₁ rightRow,
        profiledOpenLeftEmissionAlternativeOfEvaluation A strategy hwin basis
          initialCode leftReachable leftEvaluation₁ leftRow₁)
      (profiledOpenRightEmissionAlternativeOfEvaluation A strategy hwin basis
          initialCode rightReachable rightEvaluation₂ rightRow,
        profiledOpenLeftEmissionAlternativeOfEvaluation A strategy hwin basis
          initialCode leftReachable leftEvaluation₂ leftRow₂) := by
  constructor
  · intro inputTwo
    exact profiledOpenWitnessedLeftSenderOutput_crossCurrent A strategy hwin
      basis initialCode leftReachable leftEvaluation₁ leftEvaluation₂ leftRow₁
        leftRow₂ inputTwo
  · intro inputOne inputTwo
    exact profiledOpenWitnessedRightReceiverOutput_sameCurrent A strategy hwin
      basis initialCode rightReachable rightEvaluation₁ rightEvaluation₂
        rightRow inputOne inputTwo

/-! ## The four physical output laws -/

section
omit [Inhabited I]

section
omit [Inhabited Out₁] [Inhabited Out₂]

/-- Strict-right/no-receive process-one output.  Only equality of the public
right controller/query is used; the hidden current and row may differ. -/
theorem profiledOpenLocalEventEmission_noRecvOne
    {left right : ProfiledOpenLocalEventEmissionState A strategy hwin basis
      initialCode}
    (hrel : ProfiledOpenLocalEventEqOne A strategy hwin basis initialCode left
      right)
    (inputOne : In₁) (leftHidden rightHidden : In₂) :
    (profiledOpenLocalEventEmission A strategy hwin basis initialCode left
      { inputOne := inputOne, inputTwo := leftHidden, graph := .right }).1 =
    (profiledOpenLocalEventEmission A strategy hwin basis initialCode right
      { inputOne := inputOne, inputTwo := rightHidden, graph := .right }).1 := by
  exact hrel.1 inputOne

/-- Strict-left/no-receive process-two mirror. -/
theorem profiledOpenLocalEventEmission_noRecvTwo
    {left right : ProfiledOpenLocalEventEmissionState A strategy hwin basis
      initialCode}
    (hrel : ProfiledOpenLocalEventEqTwo A strategy hwin basis initialCode left
      right)
    (inputTwo : In₂) (leftHidden rightHidden : In₁) :
    (profiledOpenLocalEventEmission A strategy hwin basis initialCode left
      { inputOne := leftHidden, inputTwo := inputTwo, graph := .left }).2 =
    (profiledOpenLocalEventEmission A strategy hwin basis initialCode right
      { inputOne := rightHidden, inputTwo := inputTwo, graph := .left }).2 := by
  exact hrel.1 inputTwo

/-- On either process-one receive graph, the finite relation supplies one
left current and sticky row; exact dependent-root homogeneity supplies the
output. -/
theorem profiledOpenLocalEventEmission_recvOne
    {left right : ProfiledOpenLocalEventEmissionState A strategy hwin basis
      initialCode}
    (hrel : ProfiledOpenLocalEventEqOne A strategy hwin basis initialCode left
      right)
    (inputOne : In₁) (inputTwo : In₂) (leftGraph rightGraph : Graph)
    (hleftGraph : leftGraph = .left ∨ leftGraph = .both)
    (hrightGraph : rightGraph = .left ∨ rightGraph = .both) :
    (profiledOpenLocalEventEmission A strategy hwin basis initialCode left
      { inputOne := inputOne, inputTwo := inputTwo, graph := leftGraph }).1 =
    (profiledOpenLocalEventEmission A strategy hwin basis initialCode right
      { inputOne := inputOne, inputTwo := inputTwo, graph := rightGraph }).1 := by
  rcases hleftGraph with rfl | rfl <;>
    rcases hrightGraph with rfl | rfl
  all_goals exact hrel.2 inputOne inputTwo

/-- Process-two receive mirror. -/
theorem profiledOpenLocalEventEmission_recvTwo
    {left right : ProfiledOpenLocalEventEmissionState A strategy hwin basis
      initialCode}
    (hrel : ProfiledOpenLocalEventEqTwo A strategy hwin basis initialCode left
      right)
    (inputOne : In₁) (inputTwo : In₂) (leftGraph rightGraph : Graph)
    (hleftGraph : leftGraph = .right ∨ leftGraph = .both)
    (hrightGraph : rightGraph = .right ∨ rightGraph = .both) :
    (profiledOpenLocalEventEmission A strategy hwin basis initialCode left
      { inputOne := inputOne, inputTwo := inputTwo, graph := leftGraph }).2 =
    (profiledOpenLocalEventEmission A strategy hwin basis initialCode right
      { inputOne := inputOne, inputTwo := inputTwo, graph := rightGraph }).2 := by
  rcases hleftGraph with rfl | rfl <;>
    rcases hrightGraph with rfl | rfl
  all_goals exact hrel.2 inputOne inputTwo

end

end

/-! ## Direct bridge to the generic Mealy criterion -/

/-- Once a finite source recurrence preserves the two explicit local
relations, all four output-equality halves of `MealyLocalCongruence` are
automatic. -/
noncomputable def profiledOpenLocalEventMealyLocalCongruence
    (base : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (stateView : base.State →
      ProfiledOpenLocalEventEmissionState A strategy hwin basis initialCode)
    (hnoRecvOne : ∀ {left right},
      ProfiledOpenLocalEventEqOne A strategy hwin basis initialCode
          (stateView left) (stateView right) →
      ∀ (inputOne : In₁) (leftHidden rightHidden : In₂),
        ProfiledOpenLocalEventEqOne A strategy hwin basis initialCode
          (stateView (base.step left
            { inputOne := inputOne, inputTwo := leftHidden, graph := .right }))
          (stateView (base.step right
            { inputOne := inputOne, inputTwo := rightHidden,
              graph := .right })))
    (hnoRecvTwo : ∀ {left right},
      ProfiledOpenLocalEventEqTwo A strategy hwin basis initialCode
          (stateView left) (stateView right) →
      ∀ (inputTwo : In₂) (leftHidden rightHidden : In₁),
        ProfiledOpenLocalEventEqTwo A strategy hwin basis initialCode
          (stateView (base.step left
            { inputOne := leftHidden, inputTwo := inputTwo, graph := .left }))
          (stateView (base.step right
            { inputOne := rightHidden, inputTwo := inputTwo, graph := .left })))
    (hrecvOne : ∀ {left right},
      ProfiledOpenLocalEventEqOne A strategy hwin basis initialCode
          (stateView left) (stateView right) →
      ProfiledOpenLocalEventEqTwo A strategy hwin basis initialCode
          (stateView left) (stateView right) →
      ∀ (inputOne : In₁) (inputTwo : In₂) (leftGraph rightGraph : Graph),
        (leftGraph = .left ∨ leftGraph = .both) →
        (rightGraph = .left ∨ rightGraph = .both) →
        ProfiledOpenLocalEventEqOne A strategy hwin basis initialCode
          (stateView (base.step left
            { inputOne := inputOne, inputTwo := inputTwo,
              graph := leftGraph }))
          (stateView (base.step right
            { inputOne := inputOne, inputTwo := inputTwo,
              graph := rightGraph })))
    (hrecvTwo : ∀ {left right},
      ProfiledOpenLocalEventEqOne A strategy hwin basis initialCode
          (stateView left) (stateView right) →
      ProfiledOpenLocalEventEqTwo A strategy hwin basis initialCode
          (stateView left) (stateView right) →
      ∀ (inputOne : In₁) (inputTwo : In₂) (leftGraph rightGraph : Graph),
        (leftGraph = .right ∨ leftGraph = .both) →
        (rightGraph = .right ∨ rightGraph = .both) →
        ProfiledOpenLocalEventEqTwo A strategy hwin basis initialCode
          (stateView (base.step left
            { inputOne := inputOne, inputTwo := inputTwo,
              graph := leftGraph }))
          (stateView (base.step right
            { inputOne := inputOne, inputTwo := inputTwo,
              graph := rightGraph }))) :
    FiniteGlobalRoundMachine.MealyLocalCongruence base
      (fun state round ↦ profiledOpenLocalEventEmission A strategy hwin basis
        initialCode (stateView state) round) where
  EqOne := fun left right ↦
    ProfiledOpenLocalEventEqOne A strategy hwin basis initialCode
      (stateView left) (stateView right)
  EqTwo := fun left right ↦
    ProfiledOpenLocalEventEqTwo A strategy hwin basis initialCode
      (stateView left) (stateView right)
  reflOne := fun state ↦ profiledOpenLocalEventEqOne_refl A strategy hwin basis
    initialCode (stateView state)
  reflTwo := fun state ↦ profiledOpenLocalEventEqTwo_refl A strategy hwin basis
    initialCode (stateView state)
  noRecvOne := by
    intro left right hrel inputOne leftHidden rightHidden
    exact ⟨hnoRecvOne hrel inputOne leftHidden rightHidden,
      profiledOpenLocalEventEmission_noRecvOne A strategy hwin basis
        initialCode hrel inputOne leftHidden rightHidden⟩
  noRecvTwo := by
    intro left right hrel inputTwo leftHidden rightHidden
    exact ⟨hnoRecvTwo hrel inputTwo leftHidden rightHidden,
      profiledOpenLocalEventEmission_noRecvTwo A strategy hwin basis
        initialCode hrel inputTwo leftHidden rightHidden⟩
  recvOne := by
    intro left right hone htwo inputOne inputTwo leftGraph rightGraph hleft
      hright
    exact ⟨hrecvOne hone htwo inputOne inputTwo leftGraph rightGraph hleft
        hright,
      profiledOpenLocalEventEmission_recvOne A strategy hwin basis initialCode
        hone inputOne inputTwo leftGraph rightGraph hleft hright⟩
  recvTwo := by
    intro left right hone htwo inputOne inputTwo leftGraph rightGraph hleft
      hright
    exact ⟨hrecvTwo hone htwo inputOne inputTwo leftGraph rightGraph hleft
        hright,
      profiledOpenLocalEventEmission_recvTwo A strategy hwin basis initialCode
        htwo inputOne inputTwo leftGraph rightGraph hleft hright⟩

end

end DetParityAutomaton

end DistributedSynthesis
