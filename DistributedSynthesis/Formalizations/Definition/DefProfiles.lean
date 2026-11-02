/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Definition.DefHistory
import DistributedSynthesis.Formalizations.Definition.DefPathSummary

/-!
# Automaton profiles and exact locally uniform profile updates
-/

namespace DistributedSynthesis

universe u v w x y

/-- Definition `def:autprofile`: closed graph uncertainty is represented by a set of states. -/
structure AutomatonGraphProfile
    (State : Type u) where
  possible : Set State

/-- One-step graph-uncertainty profile update under fixed input/output letters. -/
def AutomatonGraphProfile.step
    {State : Type u} {Alphabet : Type v}
    (delta : State -> Alphabet -> State)
    (letterOfGraph : Graph -> Alphabet)
    (profile : AutomatonGraphProfile State) :
    AutomatonGraphProfile State where
  possible := { state' | ∃ state graph, state ∈ profile.possible ∧
    state' = delta state (letterOfGraph graph) }

/-- A locally uniform action assigns outputs by local-view values. -/
structure LocallyUniformAction
    (View₁ : Type u) (View₂ : Type v) (Out₁ : Type w) (Out₂ : Type x) where
  act₁ : View₁ -> Out₁
  act₂ : View₂ -> Out₂

/-- Definition `def:exactprofileupdate`: finite counterfactual histories with automaton states. -/
structure ExactProfileUpdateProblem
    (Hist : Type u) (View₁ : Type v) (View₂ : Type w)
    (State : Type x) (Out₁ : Type y) (Out₂ : Type y) where
  histFinite : Fintype Hist
  stateOf : Hist -> State
  view₁ : Hist -> View₁
  view₂ : Hist -> View₂
  transition : Hist -> Out₁ -> Out₂ -> State

attribute [instance] ExactProfileUpdateProblem.histFinite

/-- Apply a locally uniform action to an exact finite profile-update problem. -/
def exactProfileUpdate
    {Hist : Type u} {View₁ : Type v} {View₂ : Type w}
    {State : Type x} {Out₁ : Type y} {Out₂ : Type y}
    (problem : ExactProfileUpdateProblem Hist View₁ View₂ State Out₁ Out₂)
    (action : LocallyUniformAction View₁ View₂ Out₁ Out₂) :
    Hist -> State :=
  fun h => problem.transition h (action.act₁ (problem.view₁ h)) (action.act₂ (problem.view₂ h))

end DistributedSynthesis
