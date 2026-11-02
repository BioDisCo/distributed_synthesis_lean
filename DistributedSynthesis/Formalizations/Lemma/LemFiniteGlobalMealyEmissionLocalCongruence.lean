/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteGlobalMealyEmission
import DistributedSynthesis.Formalizations.Theorem.ThmFiniteGlobalLocalCongruence

/-!
# Four local-event laws localize a finite Mealy emission

The Mealy carrier computes the physical output from the source state and the
current environment letter.  Locality is therefore most naturally checked
at that transition.  A relation for each process records equality of its
finite local information.  The four laws below simultaneously preserve that
relation and equate the coordinate emitted on the corresponding local event:

* process one, no receive (`right`), with arbitrary hidden process-two input;
* process two, no receive (`left`), with arbitrary hidden process-one input;
* process one, receive (`left`/`both`), using both delivered relations;
* process two, receive (`right`/`both`), using both delivered relations.

The last emitted coordinate in `withMealyEmission` then extends each source
relation to an ordinary Moore-state local congruence.  The existing generic
belief induction yields `ReachableBeliefsUniform`; no global orientation,
leader flag, or recovered hidden bit is introduced.
-/

namespace DistributedSynthesis

universe u v w x y

namespace FiniteGlobalRoundMachine

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable [Fintype In₁] [Fintype In₂]

private def mealyRound (inputOne : In₁) (inputTwo : In₂) (graph : Graph) :
    EnvironmentRound In₁ In₂ :=
  { inputOne := inputOne
    inputTwo := inputTwo
    graph := graph }

/-- A local congruence checked directly at a finite Mealy emission.  Each
transition field contains both the next-source relation and equality of the
coordinate emitted on that process's local event. -/
structure MealyLocalCongruence
    (base : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (emit : base.State → EnvironmentRound In₁ In₂ → Out₁ × Out₂) where
  EqOne : base.State → base.State → Prop
  EqTwo : base.State → base.State → Prop
  reflOne : ∀ state, EqOne state state
  reflTwo : ∀ state, EqTwo state state
  noRecvOne : ∀ {left right}, EqOne left right →
    ∀ (inputOne : In₁) (leftHidden rightHidden : In₂),
      EqOne
          (base.step left (mealyRound inputOne leftHidden .right))
          (base.step right (mealyRound inputOne rightHidden .right)) ∧
        (emit left (mealyRound inputOne leftHidden .right)).1 =
          (emit right (mealyRound inputOne rightHidden .right)).1
  noRecvTwo : ∀ {left right}, EqTwo left right →
    ∀ (inputTwo : In₂) (leftHidden rightHidden : In₁),
      EqTwo
          (base.step left (mealyRound leftHidden inputTwo .left))
          (base.step right (mealyRound rightHidden inputTwo .left)) ∧
        (emit left (mealyRound leftHidden inputTwo .left)).2 =
          (emit right (mealyRound rightHidden inputTwo .left)).2
  recvOne : ∀ {left right}, EqOne left right → EqTwo left right →
    ∀ (inputOne : In₁) (inputTwo : In₂) (leftGraph rightGraph : Graph),
      (leftGraph = .left ∨ leftGraph = .both) →
      (rightGraph = .left ∨ rightGraph = .both) →
      EqOne
          (base.step left (mealyRound inputOne inputTwo leftGraph))
          (base.step right (mealyRound inputOne inputTwo rightGraph)) ∧
        (emit left (mealyRound inputOne inputTwo leftGraph)).1 =
          (emit right (mealyRound inputOne inputTwo rightGraph)).1
  recvTwo : ∀ {left right}, EqOne left right → EqTwo left right →
    ∀ (inputOne : In₁) (inputTwo : In₂) (leftGraph rightGraph : Graph),
      (leftGraph = .right ∨ leftGraph = .both) →
      (rightGraph = .right ∨ rightGraph = .both) →
      EqTwo
          (base.step left (mealyRound inputOne inputTwo leftGraph))
          (base.step right (mealyRound inputOne inputTwo rightGraph)) ∧
        (emit left (mealyRound inputOne inputTwo leftGraph)).2 =
          (emit right (mealyRound inputOne inputTwo rightGraph)).2

namespace MealyLocalCongruence

variable
  {base : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂}
  [Fintype Out₁] [Fintype Out₂] [Inhabited Out₁] [Inhabited Out₂]
  {emit : base.State → EnvironmentRound In₁ In₂ → Out₁ × Out₂}

/-- Extend the source relations with equality of the last emitted local
coordinate.  The four Mealy laws are exactly the four closure obligations of
the lifted Moore machine. -/
noncomputable def toLocalCongruence
    (C : MealyLocalCongruence base emit) :
    (withMealyEmission base emit).LocalCongruence
      (withMealyEmissionOutputOne emit)
      (withMealyEmissionOutputTwo emit) where
  EqOne := fun left right ↦ C.EqOne left.1 right.1 ∧ left.2.1 = right.2.1
  EqTwo := fun left right ↦ C.EqTwo left.1 right.1 ∧ left.2.2 = right.2.2
  reflOne := fun state ↦ ⟨C.reflOne state.1, rfl⟩
  reflTwo := fun state ↦ ⟨C.reflTwo state.1, rfl⟩
  outputOne_eq := fun h ↦ h.2
  outputTwo_eq := fun h ↦ h.2
  noRecvOne := by
    intro left right hrel inputOne leftHidden rightHidden
    exact C.noRecvOne hrel.1 inputOne leftHidden rightHidden
  noRecvTwo := by
    intro left right hrel inputTwo leftHidden rightHidden
    exact C.noRecvTwo hrel.1 inputTwo leftHidden rightHidden
  recvOne := by
    intro left right hone htwo inputOne inputTwo leftGraph rightGraph
      hleft hright
    exact C.recvOne hone.1 htwo.1 inputOne inputTwo leftGraph rightGraph
      hleft hright
  recvTwo := by
    intro left right hone htwo inputOne inputTwo leftGraph rightGraph
      hleft hright
    exact C.recvTwo hone.1 htwo.1 inputOne inputTwo leftGraph rightGraph
      hleft hright

/-- The four local-event Mealy laws discharge the dangerous reachable-belief
uniformity obligation of the lifted physical machine. -/
theorem reachableBeliefsUniform
    (C : MealyLocalCongruence base emit) :
    (withMealyEmission base emit).ReachableBeliefsUniform
      (withMealyEmissionOutputOne emit)
      (withMealyEmissionOutputTwo emit) :=
  reachableBeliefsUniform_of_localCongruence _ _ _ C.toLocalCongruence

end MealyLocalCongruence

end FiniteGlobalRoundMachine

end DistributedSynthesis
