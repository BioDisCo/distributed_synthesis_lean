/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmFiniteGlobalBeliefSummary
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndOverlapInvariant

/-!
# The finite global proof machine for the one-policy package

This omniscient machine is used only in the correctness proof.  Its matched
phase is finite because the pair of finite local projections determines its
constructor and data.  At an ambiguous graph it emits the two-shadow hybrid;
at a strict reversal it consumes the relevant preceding receipt bit.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 400000

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

open PairedStrategyMemory
open PairedStrategyMemory.PairedInitialProfiledRationalPackage

variable (package : PairedInitialProfiledRationalPackage A)

noncomputable instance : Fintype (EndToEndMatchedPhase A package) := by
  classical
  refine Fintype.ofInjective
    (fun phase => (phase.oneControl, phase.twoControl)) ?_
  intro left right h
  cases left <;> cases right <;>
    simp_all [EndToEndMatchedPhase.oneControl,
      EndToEndMatchedPhase.twoControl]

/-- Finite state of the global proof machine. -/
structure EndToEndGlobalPhaseState where
  phase : EndToEndMatchedPhase A package
  receivedOne : Bool
  receivedTwo : Bool
  output : Out₁ × Out₂

noncomputable instance : Fintype (EndToEndGlobalPhaseState A package) := by
  classical
  exact Fintype.ofEquiv
    ((((EndToEndMatchedPhase A package × Bool) × Bool) × (Out₁ × Out₂))) {
      toFun := fun state =>
        { phase := state.1.1.1
          receivedOne := state.1.1.2
          receivedTwo := state.1.2
          output := state.2 }
      invFun := fun state =>
        (((state.phase, state.receivedOne), state.receivedTwo), state.output)
      left_inv := by intro state; cases state; rfl
      right_inv := by intro state; cases state; rfl
    }

/-- Receipt bit produced by the current graph for process one. -/
def endToEndReceivedOneOfGraph : Graph → Bool
  | .left | .both => true
  | .right => false

/-- Receipt bit produced by the current graph for process two. -/
def endToEndReceivedTwoOfGraph : Graph → Bool
  | .right | .both => true
  | .left => false

noncomputable def endToEndGlobalRightRound
    (state : EndToEndGlobalPhaseState A package)
    (round : EnvironmentRound In₁ In₂) :
    EndToEndGlobalPhaseState A package :=
  let move := (round.inputOne, round.inputTwo)
  let continued := state.phase.continue A package move
  let reversed := state.phase.reverseRightToLeft A package move
    state.receivedOne
  let nextPhase := reversed.2.getD continued.2
  let nextOutput := match round.graph with
    | .right => continued.1
    | .left => reversed.1
    | .both => endToEndBothPhysicalOutput continued.1 reversed.1
  { phase := if round.graph = .left then nextPhase else continued.2
    receivedOne := endToEndReceivedOneOfGraph round.graph
    receivedTwo := endToEndReceivedTwoOfGraph round.graph
    output := nextOutput }

noncomputable def endToEndGlobalLeftRound
    (state : EndToEndGlobalPhaseState A package)
    (round : EnvironmentRound In₁ In₂) :
    EndToEndGlobalPhaseState A package :=
  let move := (round.inputOne, round.inputTwo)
  let continued := state.phase.continue A package move
  let reversed := state.phase.reverseLeftToRight A package
    (move.2, move.1) state.receivedTwo
  let nextPhase := reversed.2.getD continued.2
  let nextOutput := match round.graph with
    | .left => continued.1
    | .right => reversed.1
    | .both => endToEndBothPhysicalOutput reversed.1 continued.1
  { phase := if round.graph = .right then nextPhase else continued.2
    receivedOne := endToEndReceivedOneOfGraph round.graph
    receivedTwo := endToEndReceivedTwoOfGraph round.graph
    output := nextOutput }

noncomputable def endToEndGlobalPhaseRound
    (state : EndToEndGlobalPhaseState A package)
    (round : EnvironmentRound In₁ In₂) :
    EndToEndGlobalPhaseState A package :=
  match state.phase with
  | .firstRight _ _ _ | .rightOriginRight _ _ _ |
      .leftOriginRight _ _ _ =>
      endToEndGlobalRightRound A package state round
  | .firstLeft _ _ _ | .rightOriginLeft _ _ _ |
      .leftOriginLeft _ _ _ =>
      endToEndGlobalLeftRound A package state round

noncomputable def endToEndGlobalPhaseMachine
    (initialPhase : EndToEndMatchedPhase A package)
    (receivedOne receivedTwo : Bool) :
    FiniteGlobalRoundMachine In₁ In₂ where
  State := EndToEndGlobalPhaseState A package
  stateFinite := inferInstance
  initial :=
    { phase := initialPhase
      receivedOne := receivedOne
      receivedTwo := receivedTwo
      output := default }
  step := endToEndGlobalPhaseRound A package

def endToEndGlobalOutputOne
    (state : EndToEndGlobalPhaseState A package) : Out₁ := state.output.1

def endToEndGlobalOutputTwo
    (state : EndToEndGlobalPhaseState A package) : Out₂ := state.output.2

/-- The exact local-uniformity obligation for the assembled package machine. -/
def EndToEndGlobalBeliefsUniform
    (initialPhase : EndToEndMatchedPhase A package)
    (receivedOne receivedTwo : Bool) : Prop :=
  let G := endToEndGlobalPhaseMachine A package initialPhase receivedOne
    receivedTwo
  G.ReachableBeliefsUniform
    (endToEndGlobalOutputOne A package)
    (endToEndGlobalOutputTwo A package)

end


end DetParityAutomaton

end DistributedSynthesis
