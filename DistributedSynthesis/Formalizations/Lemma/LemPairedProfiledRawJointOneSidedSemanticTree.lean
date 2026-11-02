/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedThreadSystem
import DistributedSynthesis.Formalizations.Lemma.LemSourceFreeBeliefNodeRationalization

/-!
# The recursive one-sided raw joint semantic tree

The simultaneous raw move is selected before Nature chooses an actual block
side.  The semantic successor, however, keeps only the lane produced by that
side.  This file iterates that corrected operation.

An exact semantic state carries the literal strategy family together with the
fact that every raw direction has a common source.  This is automatic after
the first one-sided step: the opposite lane is empty.  Consequently every
later step has an unconditional source-free code equation.  No rational run,
finite lambda controller, current leader, or process-visible side occurs in
this construction.

The final certificate constructor deliberately leaves universal branch parity
as an explicit argument.  The next file proves it by following one persistent
lineage through the literal `PairedStrategyMemory` children.  Separating T1
from parity makes the former recursion obstruction impossible to hide in an
acceptance hypothesis.
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

/-! ## Exact recursively closed semantic states -/

/-- One raw semantic family on which every possible next pivot has a literal
common source.  One-sided families satisfy this field vacuously on the absent
lane, while the live lane still carries the real strategy histories. -/
structure ProfiledRawJointOneSidedSemanticState
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂) where
  family : ProfiledRawJointSemanticFamily A strategy (I := I)
  exactFibre : ∀ direction : ProfiledRawJointFamilyDirection
    (I := I) (In₁ := In₁) (In₂ := In₂),
      family.ExactFibreAt A direction

/-- Nature advances exactly the selected physical side.  Both raw lambdas
were already present in `family.move`; only the semantic target is one-sided.
-/
def ProfiledRawJointOneSidedSemanticState.step
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (state : ProfiledRawJointOneSidedSemanticState A strategy (I := I))
    (actual : ProfiledRawJointActualDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointOneSidedSemanticState A strategy (I := I) :=
  match actual.side with
  | .right =>
      { family := state.family.rightActualChild A actual.direction
        exactFibre := state.family.rightActualChild_exactFibreAt A
          actual.direction }
  | .left =>
      { family := state.family.leftActualChild A actual.direction
        exactFibre := state.family.leftActualChild_exactFibreAt A
          actual.direction }

/-- Exact finite erasure of one semantic state. -/
noncomputable def ProfiledRawJointOneSidedSemanticState.code
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (state : ProfiledRawJointOneSidedSemanticState A strategy (I := I)) :
    ProfiledRawJointIncidenceCode A (I := I) :=
  state.family.incidenceCode A

/-- The whole raw simultaneous lambda family chosen before the actual side.
-/
def ProfiledRawJointOneSidedSemanticState.move
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (state : ProfiledRawJointOneSidedSemanticState A strategy (I := I)) :
    ProfiledRawJointLambdaFamilyMove A (I := I) :=
  state.family.move A

/-- Source-free legality ignores only the incidence proof coordinate.  The
complete raw lambda law is checked against the finite family code. -/
def ProfiledRawJointIncidenceMoveValid
    (code : ProfiledRawJointIncidenceCode A (I := I))
    (move : ProfiledRawJointLambdaFamilyMove A (I := I)) : Prop :=
  move.Valid A code.family

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype I] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] in
/-- A winning distributed strategy makes the raw move at every exact state
legal. -/
theorem ProfiledRawJointOneSidedSemanticState.move_valid_of_winning
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (state : ProfiledRawJointOneSidedSemanticState A strategy (I := I)) :
    ProfiledRawJointIncidenceMoveValid A (state.code A) (state.move A) := by
  exact state.family.move_valid_of_winning A hwin

/-! ## The unconditional T1 equation -/

omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] in
/-- Every semantic step erases to the one-sided finite successor.  The proof
chooses a literal common source only in `Prop`; the source is absent from the
finite code and from the transition function. -/
theorem ProfiledRawJointOneSidedSemanticState.step_code
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (state : ProfiledRawJointOneSidedSemanticState A strategy (I := I))
    (actual : ProfiledRawJointActualDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    (state.step A actual).code A =
      profiledRawJointOneSidedNext A (state.code A) (state.move A) actual := by
  classical
  let common := Classical.choice
    (state.family.exists_commonSourceAt A actual.direction
      (state.exactFibre actual.direction))
  cases hside : actual.side with
  | right =>
      simpa [ProfiledRawJointOneSidedSemanticState.step,
        ProfiledRawJointOneSidedSemanticState.code,
        ProfiledRawJointOneSidedSemanticState.move,
        profiledRawJointOneSidedNext, hside] using
        state.family.rightActualChild_incidenceCode_eq A actual.direction
          common
  | left =>
      simpa [ProfiledRawJointOneSidedSemanticState.step,
        ProfiledRawJointOneSidedSemanticState.code,
        ProfiledRawJointOneSidedSemanticState.move,
        profiledRawJointOneSidedNext, hside] using
        state.family.leftActualChild_incidenceCode_eq A actual.direction
          common

/-! ## Recursive source-free semantic tree -/

/-- The full exact unfolding under one fixed raw winning strategy. -/
def profiledRawJointOneSidedSemanticTree
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := I)) :
    SourceFreeBeliefSemanticTree
      (ProfiledRawJointActualDirection
        (I := I) (In₁ := In₁) (In₂ := In₂))
      (ProfiledRawJointLambdaFamilyMove A (I := I))
      (ProfiledRawJointIncidenceCode A (I := I)) where
  Semantic := ProfiledRawJointOneSidedSemanticState A strategy (I := I)
  initial := initial
  step := ProfiledRawJointOneSidedSemanticState.step A
  code := ProfiledRawJointOneSidedSemanticState.code A
  move := ProfiledRawJointOneSidedSemanticState.move A

omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] in
@[simp] theorem profiledRawJointOneSidedSemanticTree_initial_code
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := I)) :
    let raw := profiledRawJointOneSidedSemanticTree A initial
    raw.code raw.initial = initial.code A :=
  rfl

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype I] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] in
/-- Node-local raw legality throughout the recursive unfolding. -/
theorem profiledRawJointOneSidedSemanticTree_valid
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := I))
    (node : TreeNode (ProfiledRawJointActualDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))) :
    let raw := profiledRawJointOneSidedSemanticTree A initial
    ProfiledRawJointIncidenceMoveValid A
      (raw.code (raw.stateAt node)) (raw.move (raw.stateAt node)) := by
  exact ProfiledRawJointOneSidedSemanticState.move_valid_of_winning A hwin _

omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] in
/-- The recursive tree satisfies Bérard's source-free T1 law at every node.
-/
theorem profiledRawJointOneSidedSemanticTree_next_code
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := I))
    (node : TreeNode (ProfiledRawJointActualDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)))
    (actual : ProfiledRawJointActualDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    let raw := profiledRawJointOneSidedSemanticTree A initial
    raw.code (raw.step (raw.stateAt node) actual) =
      profiledRawJointOneSidedNext A
        (raw.code (raw.stateAt node)) (raw.move (raw.stateAt node)) actual := by
  exact ProfiledRawJointOneSidedSemanticState.step_code A _ actual

/-! ## Exact handoff to the generic source-free rationalization -/

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Once branch parity is supplied, the semantic tree is a complete generic
source-free certificate.  T1 and legality are discharged above and do not
occur in `haccepts`. -/
theorem profiledRawJointOneSidedSemanticCertificate_of_accepts
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := I))
    (haccepts : ∀ branch : Nat → ProfiledRawJointActualDirection
        (I := I) (In₁ := In₁) (In₂ := In₂),
      (profiledRawJointOneSidedThreadSystem A (initial.code A)).universalRunDPA.Accepts
        (observableThreadWord
          (profiledRawJointOneSidedSemanticTree A initial).moveTree branch)) :
    SourceFreeBeliefSemanticCertificate
      (profiledRawJointOneSidedThreadSystem A (initial.code A))
      (initial.code A)
      (ProfiledRawJointIncidenceMoveValid A)
      (profiledRawJointOneSidedNext A)
      (profiledRawJointOneSidedSemanticTree A initial) :=
  { initial_code := rfl
    valid := profiledRawJointOneSidedSemanticTree_valid A hwin initial
    next_code := profiledRawJointOneSidedSemanticTree_next_code A initial
    accepts := haccepts }

end

end DetParityAutomaton

end DistributedSynthesis
