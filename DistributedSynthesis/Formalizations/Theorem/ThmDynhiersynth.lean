/- Project authors: see AUTHORS.md at the repository root. -/

import Mathlib.Data.Fintype.Basic
import DistributedSynthesis.Formalizations.Theorem.ThmDynamicHierarchyFiniteState

/-!
# Finite dynamic-hierarchy synthesis bridge

This file isolates the finite-game theorem used by the paper.  The game is
represented in solved finite normal form: finite controller strategies, finite
environment strategies, and a decidable parity-outcome relation.  The theorem
then proves realizability is decidable by finite search.
-/

namespace DistributedSynthesis

universe u v u' v'

/-!
## The actual finite-state theorem boundary

The solved normal form below is useful once finite strategy carriers have
already been constructed.  The cited dynamic-hierarchy theorem additionally
has to construct those carriers from a finite concurrent game whose
perfect-recall information sets are comparable after every history.  The
following proposition records that stronger statement without conflating it
with memorylessness on the original observations.
-/

/-- Lean statement of the output promised by Theorem 10 of
Berwanger--Mathew--van den Bogaard: every finite game with dynamic
hierarchical information has a decision procedure, and every realizable such
game has finite Moore-controller realizers. -/
def DynamicHierarchyFiniteStateSolvable : Prop :=
  ∀ game : FiniteConcurrentGame.{u},
    game.DynamicHierarchy ->
      Nonempty game.FiniteStateSynthesisCertificate

/-- Elimination rule for an implementation or imported instance of the cited
dynamic-hierarchy theorem. -/
theorem finiteStateSynthesisCertificate_of_dynamicHierarchy
    (theorem10 : DynamicHierarchyFiniteStateSolvable.{u})
    (game : FiniteConcurrentGame.{u}) (hhierarchy : game.DynamicHierarchy) :
    Nonempty game.FiniteStateSynthesisCertificate :=
  theorem10 game hhierarchy

/--
A finite dynamic-hierarchy parity game after the standard finite-game
construction has reduced perfect-recall strategies to a finite strategy arena.

The `dynamicHierarchy` and `parityObjective` fields are applicability
certificates for the external hierarchy theorem; the finite-search decidability
proof below uses the finite strategy carriers and the decidable `wins` relation.
-/
structure FiniteDynamicHierarchyParityGame where
  ControllerStrategy : Type u
  EnvironmentStrategy : Type v
  controllerFinite : Fintype ControllerStrategy
  environmentFinite : Fintype EnvironmentStrategy
  wins : ControllerStrategy -> EnvironmentStrategy -> Prop
  winsDecidable : ∀ σ τ, Decidable (wins σ τ)
  dynamicHierarchy : Prop
  parityObjective : Prop
  dynamicHierarchy_proof : dynamicHierarchy
  parityObjective_proof : parityObjective

attribute [instance] FiniteDynamicHierarchyParityGame.controllerFinite
attribute [instance] FiniteDynamicHierarchyParityGame.environmentFinite
attribute [instance] FiniteDynamicHierarchyParityGame.winsDecidable

/-- Realizability in the finite game: one controller strategy wins against all environments. -/
def FiniteDynamicHierarchyParityGame.realizable
    (game : FiniteDynamicHierarchyParityGame.{u, v}) : Prop :=
  ∃ σ : game.ControllerStrategy, ∀ τ : game.EnvironmentStrategy, game.wins σ τ

/--
Universe lift for finite games.  This is only bookkeeping: strategies are
wrapped in `ULift`, and the winning relation is transported through `.down`.
-/
def FiniteDynamicHierarchyParityGame.lift
    (game : FiniteDynamicHierarchyParityGame.{u, v}) :
    FiniteDynamicHierarchyParityGame.{max u u', max v v'} where
  ControllerStrategy := ULift.{max u u'} game.ControllerStrategy
  EnvironmentStrategy := ULift.{max v v'} game.EnvironmentStrategy
  controllerFinite := inferInstance
  environmentFinite := inferInstance
  wins σ τ := game.wins σ.down τ.down
  winsDecidable σ τ := game.winsDecidable σ.down τ.down
  dynamicHierarchy := game.dynamicHierarchy
  parityObjective := game.parityObjective
  dynamicHierarchy_proof := game.dynamicHierarchy_proof
  parityObjective_proof := game.parityObjective_proof

/-- The finite-game universe lift preserves realizability. -/
theorem FiniteDynamicHierarchyParityGame.lift_realizable_iff
    (game : FiniteDynamicHierarchyParityGame.{u, v}) :
    (FiniteDynamicHierarchyParityGame.lift.{u, v, u', v'} game).realizable ↔
      game.realizable := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨σ.down, fun τ => hσ (ULift.up τ)⟩
  · rintro ⟨σ, hσ⟩
    exact ⟨ULift.up σ, fun τ => hσ τ.down⟩

/--
Theorem `thm:dynhiersynth`: once the dynamic-hierarchy construction has produced
finite strategy spaces and a decidable parity-outcome relation, realizability is
decidable by finite search.
-/
def finite_dynamic_hierarchy_parity_game_decidable
    (game : FiniteDynamicHierarchyParityGame.{u, v}) :
    Decidable game.realizable := by
  letI : Fintype game.ControllerStrategy := game.controllerFinite
  letI : Fintype game.EnvironmentStrategy := game.environmentFinite
  letI : ∀ σ τ, Decidable (game.wins σ τ) := game.winsDecidable
  haveI : DecidablePred (fun σ : game.ControllerStrategy =>
      ∀ τ : game.EnvironmentStrategy, game.wins σ τ) := by
    intro σ
    exact Fintype.decidableForallFintype
  exact Fintype.decidableExistsFintype

/-- The same theorem packaged with the paper's hierarchy and parity side conditions. -/
theorem dynamic_hierarchy_synthesis_bridge
    (game : FiniteDynamicHierarchyParityGame.{u, v}) :
    game.dynamicHierarchy ∧
      game.parityObjective ∧
      Nonempty (Decidable game.realizable) := by
  exact
    ⟨game.dynamicHierarchy_proof,
      game.parityObjective_proof,
      ⟨finite_dynamic_hierarchy_parity_game_decidable game⟩⟩

end DistributedSynthesis
