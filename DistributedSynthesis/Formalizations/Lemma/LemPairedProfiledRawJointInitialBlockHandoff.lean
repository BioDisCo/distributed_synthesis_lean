/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedInitialState
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointUnitPolicyTargetProjection
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledGuardedHandoff

/-!
# Initial-block boundaries as singleton raw-joint roots

The round-zero root `profiledRawJointInitialOneSidedState` is the boundary
state for a one-round initial block.  A longer homogeneous initial block has
the same shape, but its common base is the generated strict prefix and its
carried automaton root is the minimum along that prefix.  This file records
that distinction and identifies the finite projection of every such boundary
with the existing profiled initial-handoff target.

The selected side is proof-tree data.  An initial-left boundary carries the
process-one/right slot, hence side `.right`; an initial-right boundary carries
the process-two/left slot, hence side `.left`.  The initial row does not enter
the boundary state: both rows stage the same target in the existing initial
forest.
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

/-! ## Literal common-base worlds at an initial boundary -/

/-- Common-base world staged after a possible final round of the initial
left block. -/
def profiledRawJointInitialLeftBoundaryWorld
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    ProfiledRawJointCommonBaseWorld A strategy where
  base := extendPrefix strategy [] (past.map leftEnvironment)
  base_generated := strategyGenerated_extendPrefix_basic strategy
    StrategyGeneratedPrefix.empty _
  inputOne := move.1
  inputTwo := move.2
  root := blockMinState A A.initial
    (extendPrefix strategy [] (past.map leftEnvironment))

/-- Common-base world staged after a possible final round of the initial
right block. -/
def profiledRawJointInitialRightBoundaryWorld
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    ProfiledRawJointCommonBaseWorld A strategy where
  base := extendPrefix strategy [] (past.map rightEnvironment)
  base_generated := strategyGenerated_extendPrefix_basic strategy
    StrategyGeneratedPrefix.empty _
  inputOne := move.2
  inputTwo := move.1
  root := blockMinState A A.initial
    (extendPrefix strategy [] (past.map rightEnvironment))

/-- Singleton recurrent source staged by an initial-left boundary. -/
def profiledRawJointInitialLeftBoundaryState
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    ProfiledRawJointOneSidedSemanticState A strategy (I := Unit) :=
  (profiledRawJointInitialLeftBoundaryWorld A strategy past move).oneSidedState
    A .right

/-- Singleton recurrent source staged by an initial-right boundary. -/
def profiledRawJointInitialRightBoundaryState
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    ProfiledRawJointOneSidedSemanticState A strategy (I := Unit) :=
  (profiledRawJointInitialRightBoundaryWorld A strategy past move).oneSidedState
    A .left

/-! ## Exact finite projection to the existing initial seam -/

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- The raw-joint code at an initial-left boundary projects to exactly the
profiled target already used by the delayed initial handoff. -/
theorem profiledRawJointInitialLeftBoundaryState_projection
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    profiledRawJointUnitLeftTargetProjection A
        ((profiledRawJointInitialLeftBoundaryState A strategy past move).code A) =
      initialLeftProfiledTarget A strategy past move := by
  rfl

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Initial-right mirror. -/
theorem profiledRawJointInitialRightBoundaryState_projection
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    profiledRawJointUnitRightTargetProjection A
        ((profiledRawJointInitialRightBoundaryState A strategy past move).code A) =
      initialRightProfiledTarget A strategy past move := by
  rfl

/-! ## The round-zero root is precisely the empty-past special case -/

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- For a one-round initial-left block, the boundary source is the existing
round-zero singleton root with hidden side `.right`. -/
theorem profiledRawJointInitialLeftBoundaryState_nil
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (move : In₁ × In₂) :
    profiledRawJointInitialLeftBoundaryState A strategy [] move =
      profiledRawJointInitialOneSidedState A strategy .right move.1 move.2 := by
  rfl

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- One-round initial-right mirror; note the input-pair swap. -/
theorem profiledRawJointInitialRightBoundaryState_nil
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (move : In₂ × In₁) :
    profiledRawJointInitialRightBoundaryState A strategy [] move =
      profiledRawJointInitialOneSidedState A strategy .left move.2 move.1 := by
  rfl

/-! ## Unconditional provenance policies at every genuine boundary -/

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Every genuine initial-left boundary, not just the empty-past case,
supplies a Unit provenance policy rooted at its literal boundary code. -/
theorem nonempty_profiledRawJointInitialLeftBoundaryPolicy
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    Nonempty (ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      ((profiledRawJointInitialLeftBoundaryState A strategy past move).code A)) :=
  nonempty_profiledRawJointOneSidedProvenanceRationalPolicy A strategy hwin _

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Initial-right mirror. -/
theorem nonempty_profiledRawJointInitialRightBoundaryPolicy
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    Nonempty (ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      ((profiledRawJointInitialRightBoundaryState A strategy past move).code A)) :=
  nonempty_profiledRawJointOneSidedProvenanceRationalPolicy A strategy hwin _

end

end DetParityAutomaton

end DistributedSynthesis
