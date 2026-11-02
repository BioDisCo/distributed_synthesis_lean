/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmFiniteGlobalBeliefSummary
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOperationalDiamond

/-!
# The finite global profiled recurrent machine

This omniscient proof machine follows the actually selected strict phase.  It
is not a distributed implementation and is never offered to either process.
Its purpose is to give the finite belief construction a concrete state space.
At `both`, it retains the current phase, emits the already verified hybrid
physical output, and records the fresh receipt bits.  At a strict reversal it
uses the relevant preceding receipt bit.

The exact remaining dangerous-zone statement is
`ProfiledGlobalBeliefsUniform`: both locally computed beliefs must prescribe
one output.  Unlike the rejected exact-pair invariant, this statement does
not demand equality of the hidden global phase constructors.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

section

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]
variable (firstBank : FiniteProfiledGuardedFirstControllerBank A)

/-- The proof-level matched phase is finite because its two local projections
determine it; proof fields are propositionally irrelevant. -/
noncomputable instance : Fintype (ProfiledMatchedPhase A firstBank) := by
  classical
  refine Fintype.ofInjective
    (fun phase => (phase.oneControl, phase.twoControl)) ?_
  intro left right h
  cases left <;> cases right <;>
    simp_all [ProfiledMatchedPhase.oneControl,
      ProfiledMatchedPhase.twoControl]

/-- Finite proof state of the recurrent global machine. -/
structure ProfiledGlobalPhaseState where
  phase : ProfiledMatchedPhase A firstBank
  receivedOne : Bool
  receivedTwo : Bool
  output : Out₁ × Out₂

noncomputable instance : Fintype (ProfiledGlobalPhaseState A firstBank) := by
  classical
  exact Fintype.ofEquiv
    (((ProfiledMatchedPhase A firstBank × Bool) × Bool) × (Out₁ × Out₂)) {
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
def receivedOneOfGraph : Graph → Bool
  | .left | .both => true
  | .right => false

/-- Receipt bit produced by the current graph for process two. -/
def receivedTwoOfGraph : Graph → Bool
  | .right | .both => true
  | .left => false

/-- Global step while the retained proof phase is right-oriented. -/
noncomputable def profiledGlobalRightRound
    (state : ProfiledGlobalPhaseState A firstBank)
    (round : EnvironmentRound In₁ In₂) :
    ProfiledGlobalPhaseState A firstBank :=
  let move := (round.inputOne, round.inputTwo)
  let continued := state.phase.continue A firstBank move
  let reversed := state.phase.reverseRightToLeft A firstBank move
    state.receivedOne
  let nextPhase := reversed.2.getD continued.2
  let nextOutput := match round.graph with
    | .right => continued.1
    | .left => reversed.1
    | .both => profiledBothPhysicalOutput continued.1 reversed.1
  { phase := if round.graph = .left then nextPhase else continued.2
    receivedOne := receivedOneOfGraph round.graph
    receivedTwo := receivedTwoOfGraph round.graph
    output := nextOutput }

/-- Left-oriented mirror. -/
noncomputable def profiledGlobalLeftRound
    (state : ProfiledGlobalPhaseState A firstBank)
    (round : EnvironmentRound In₁ In₂) :
    ProfiledGlobalPhaseState A firstBank :=
  let move := (round.inputOne, round.inputTwo)
  let continued := state.phase.continue A firstBank move
  let reversed := state.phase.reverseLeftToRight A firstBank
    (move.2, move.1) state.receivedTwo
  let nextPhase := reversed.2.getD continued.2
  let nextOutput := match round.graph with
    | .left => continued.1
    | .right => reversed.1
    | .both => profiledBothPhysicalOutput reversed.1 continued.1
  { phase := if round.graph = .right then nextPhase else continued.2
    receivedOne := receivedOneOfGraph round.graph
    receivedTwo := receivedTwoOfGraph round.graph
    output := nextOutput }

/-- Complete finite global recurrent step, dispatching only on the proof-side
phase constructor and the real graph. -/
noncomputable def profiledGlobalPhaseRound
    (state : ProfiledGlobalPhaseState A firstBank)
    (round : EnvironmentRound In₁ In₂) :
    ProfiledGlobalPhaseState A firstBank :=
  match state.phase with
  | .firstRight _ _ _ | .bankRight _ _ _ =>
      profiledGlobalRightRound A firstBank state round
  | .firstLeft _ _ _ | .bankLeft _ _ _ =>
      profiledGlobalLeftRound A firstBank state round

/-- The recurrent global machine from any already synchronized phase. -/
noncomputable def profiledGlobalPhaseMachine
    (initialPhase : ProfiledMatchedPhase A firstBank)
    (receivedOne receivedTwo : Bool) :
    FiniteGlobalRoundMachine In₁ In₂ where
  State := ProfiledGlobalPhaseState A firstBank
  stateFinite := inferInstance
  initial :=
    { phase := initialPhase
      receivedOne := receivedOne
      receivedTwo := receivedTwo
      output := default }
  step := profiledGlobalPhaseRound A firstBank

/-- Process-one output stored in the global Moore state. -/
def profiledGlobalOutputOne
    (state : ProfiledGlobalPhaseState A firstBank) : Out₁ := state.output.1

/-- Process-two output stored in the global Moore state. -/
def profiledGlobalOutputTwo
    (state : ProfiledGlobalPhaseState A firstBank) : Out₂ := state.output.2

/-- **The dangerous-zone target.**  Starting from a synchronized recurrent
phase, the finite beliefs of the global profiled machine are output-uniform
for both processes after every environment prefix. -/
def ProfiledGlobalBeliefsUniform
    (initialPhase : ProfiledMatchedPhase A firstBank)
    (receivedOne receivedTwo : Bool) : Prop :=
  let G := profiledGlobalPhaseMachine A firstBank initialPhase receivedOne
    receivedTwo
  G.ReachableBeliefsUniform
    (profiledGlobalOutputOne A firstBank)
    (profiledGlobalOutputTwo A firstBank)

end


end


end DetParityAutomaton

end DistributedSynthesis
