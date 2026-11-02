/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Definition.DefEpochAbstractions
import DistributedSynthesis.Formalizations.Lemma.LemRotatingtarget
import DistributedSynthesis.Formalizations.Theorem.ThmDynhiersynth

/-!
# Finite hierarchy-preserving A-index implies decidability
-/

namespace DistributedSynthesis

universe u v a b

/-- Semantic data of an effective finite hierarchy-preserving `A`-index. -/
structure FiniteAIndexSemantics
    (Config : Type u)
    (AContinuation : Config -> Config -> Prop) where
  Quotient : Type v
  quotientFinite : Fintype Quotient
  classOf : Config -> Quotient
  transitionRelationEffective : Prop
  finiteNonFringeSummariesHierarchical : Prop
  olderReceiptTagsRecoverable : Prop
  transitionRelationEffective_proof : transitionRelationEffective
  finiteNonFringeSummariesHierarchical_proof : finiteNonFringeSummariesHierarchical
  olderReceiptTagsRecoverable_proof : olderReceiptTagsRecoverable
  quotientPreservesContinuationGames :
    ∀ c c', classOf c = classOf c' -> AContinuation c c'

attribute [instance] FiniteAIndexSemantics.quotientFinite

/--
Semantic finite-index core of Theorem `thm:finiteAindex`: the quotient is finite
and equality of quotient classes preserves continuation games.
-/
theorem finite_A_index_semantic_core
    {Config : Type u} {AContinuation : Config -> Config -> Prop}
    (sem : FiniteAIndexSemantics Config AContinuation) :
    Nonempty (Fintype sem.Quotient) ∧
      sem.transitionRelationEffective ∧
      sem.finiteNonFringeSummariesHierarchical ∧
      sem.olderReceiptTagsRecoverable ∧
      ∀ c c', sem.classOf c = sem.classOf c' -> AContinuation c c' := by
  exact
    ⟨⟨inferInstance⟩,
      sem.transitionRelationEffective_proof,
      sem.finiteNonFringeSummariesHierarchical_proof,
      sem.olderReceiptTagsRecoverable_proof,
      sem.quotientPreservesContinuationGames⟩

/--
Finite `A`-index plus a constructed finite dynamic-hierarchy parity game yields
the final decidability conclusion via `thm:dynhiersynth`.
-/
theorem finite_A_index_to_decidability_via_finite_game
    {Config : Type u} {AContinuation : Config -> Config -> Prop}
    (sem : FiniteAIndexSemantics Config AContinuation)
    (game : FiniteDynamicHierarchyParityGame.{a, b}) :
    game.dynamicHierarchy ∧
      game.parityObjective ∧
      Nonempty (Decidable game.realizable) := by
  exact dynamic_hierarchy_synthesis_bridge game

/-- Certificate for applying the finite hierarchy-preserving `A`-index theorem. -/
structure FiniteAIndexDecisionCertificate
    (Config : Type u)
    (Realizable : Prop) where
  Quotient : Type v
  quotientFinite : Fintype Quotient
  classOf : Config -> Quotient
  quotientPreservesContinuationGames : Prop
  transitionRelationEffective : Prop
  finiteNonFringeSummariesHierarchical : Prop
  olderReceiptTagsRecoverable : Prop
  finiteGame : FiniteDynamicHierarchyParityGame.{a, b}
  finiteGameRealizableIff : finiteGame.realizable ↔ Realizable
  quotientPreservesContinuationGames_proof : quotientPreservesContinuationGames
  transitionRelationEffective_proof : transitionRelationEffective
  finiteNonFringeSummariesHierarchical_proof : finiteNonFringeSummariesHierarchical
  olderReceiptTagsRecoverable_proof : olderReceiptTagsRecoverable

attribute [instance] FiniteAIndexDecisionCertificate.quotientFinite

/--
Paper-facing Theorem `thm:finiteAindex`: finite effective `A`-index plus
hierarchical finite summaries yields a decision procedure.
-/
theorem finite_hierarchy_preserving_A_index_implies_decidability
    {Config : Type u} {Realizable : Prop}
    (cert : FiniteAIndexDecisionCertificate Config Realizable) :
    Nonempty (Fintype cert.Quotient) ∧
      cert.quotientPreservesContinuationGames ∧
      cert.transitionRelationEffective ∧
      cert.finiteNonFringeSummariesHierarchical ∧
      cert.olderReceiptTagsRecoverable ∧
      Nonempty (Decidable Realizable) := by
  let finiteGameDecision := finite_dynamic_hierarchy_parity_game_decidable cert.finiteGame
  have realizableDecision : Decidable Realizable := by
    cases finiteGameDecision with
    | isTrue h =>
        exact isTrue (cert.finiteGameRealizableIff.mp h)
    | isFalse h =>
        exact isFalse (fun hRealizable => h (cert.finiteGameRealizableIff.mpr hRealizable))
  exact
    ⟨⟨inferInstance⟩,
      cert.quotientPreservesContinuationGames_proof,
      cert.transitionRelationEffective_proof,
      cert.finiteNonFringeSummariesHierarchical_proof,
      cert.olderReceiptTagsRecoverable_proof,
      ⟨realizableDecision⟩⟩

/--
Build a finite `A`-index decision certificate from a semantic rotating
access-state map.

This is the constructive handoff used by the no-direct-reversal route: once the
paper construction supplies a finite access-state map whose fibers refine
continuation equivalence, the generic finite-`A`-index certificate is just the
same finite state space plus the compiled finite game and realizability
equivalence.
-/
def finiteAIndexDecisionCertificateOfRotatingAccessState
    {Config : Type u}
    {AContinuation : Config -> Config -> Prop}
    {Realizable : Prop}
    (sem : RotatingAccessStateSemantics.{u, v} Config AContinuation)
    (transitionRelationEffective : Prop)
    (transitionRelationEffective_proof : transitionRelationEffective)
    (finiteNonFringeSummariesHierarchical : Prop)
    (finiteNonFringeSummariesHierarchical_proof :
      finiteNonFringeSummariesHierarchical)
    (olderReceiptTagsRecoverable : Prop)
    (olderReceiptTagsRecoverable_proof : olderReceiptTagsRecoverable)
    (finiteGame : FiniteDynamicHierarchyParityGame.{a, b})
    (finiteGameRealizableIff : finiteGame.realizable ↔ Realizable) :
    FiniteAIndexDecisionCertificate.{u, v, a, b} Config Realizable where
  Quotient := sem.State
  quotientFinite := sem.stateFinite
  classOf := sem.accessState
  quotientPreservesContinuationGames :=
    ∀ c c', sem.accessState c = sem.accessState c' -> AContinuation c c'
  transitionRelationEffective := transitionRelationEffective
  finiteNonFringeSummariesHierarchical := finiteNonFringeSummariesHierarchical
  olderReceiptTagsRecoverable := olderReceiptTagsRecoverable
  finiteGame := finiteGame
  finiteGameRealizableIff := finiteGameRealizableIff
  quotientPreservesContinuationGames_proof :=
    sem.refinesAContinuation
  transitionRelationEffective_proof := transitionRelationEffective_proof
  finiteNonFringeSummariesHierarchical_proof :=
    finiteNonFringeSummariesHierarchical_proof
  olderReceiptTagsRecoverable_proof := olderReceiptTagsRecoverable_proof

/--
Decidability directly from a semantic rotating access-state map and the finite
game/equivalence package.
-/
noncomputable def decidability_of_rotating_access_state
    {Config : Type u}
    {AContinuation : Config -> Config -> Prop}
    {Realizable : Prop}
    (sem : RotatingAccessStateSemantics.{u, v} Config AContinuation)
    (transitionRelationEffective : Prop)
    (transitionRelationEffective_proof : transitionRelationEffective)
    (finiteNonFringeSummariesHierarchical : Prop)
    (finiteNonFringeSummariesHierarchical_proof :
      finiteNonFringeSummariesHierarchical)
    (olderReceiptTagsRecoverable : Prop)
    (olderReceiptTagsRecoverable_proof : olderReceiptTagsRecoverable)
    (finiteGame : FiniteDynamicHierarchyParityGame.{a, b})
    (finiteGameRealizableIff : finiteGame.realizable ↔ Realizable) :
    Decidable Realizable := by
  let cert :=
    finiteAIndexDecisionCertificateOfRotatingAccessState
      sem
      transitionRelationEffective
      transitionRelationEffective_proof
      finiteNonFringeSummariesHierarchical
      finiteNonFringeSummariesHierarchical_proof
      olderReceiptTagsRecoverable
      olderReceiptTagsRecoverable_proof
      finiteGame
      finiteGameRealizableIff
  let finiteGameDecision := finite_dynamic_hierarchy_parity_game_decidable cert.finiteGame
  cases finiteGameDecision with
  | isTrue h =>
      exact isTrue (cert.finiteGameRealizableIff.mp h)
  | isFalse h =>
      exact isFalse (fun hRealizable =>
        h (cert.finiteGameRealizableIff.mpr hRealizable))

end DistributedSynthesis
