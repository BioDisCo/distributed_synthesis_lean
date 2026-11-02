/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Definition.DefPathSummary

/-!
# Finite tree CSP

This file formalizes the finite-search core of `lem:treecsp`: a finite
process-owned constraint tree with finite output alphabets has a decidable
satisfying labeling problem.
-/

namespace DistributedSynthesis

universe u v w

namespace RootedConstraintTree

/--
A decidable pair-indexed version of `Satisfying`.  It replaces the dependent
edge-proof quantifier by an `if` over the decidable edge relation.
-/
def SatisfyingByPairs
    {Out₁ : Type u} {Out₂ : Type v}
    (T : RootedConstraintTree.{u, v, w} Out₁ Out₂)
    [DecidableRel T.edge]
    (label : T.Labeling) :
    Prop :=
  ∀ a b,
    if h : T.edge a b then
      T.edgeRel a b h (label a) (label b)
    else
      True

/-- The pair-indexed CSP predicate is equivalent to the semantic edge predicate. -/
theorem satisfyingByPairs_iff
    {Out₁ : Type u} {Out₂ : Type v}
    (T : RootedConstraintTree.{u, v, w} Out₁ Out₂)
    [DecidableRel T.edge]
    (label : T.Labeling) :
    T.SatisfyingByPairs label ↔ T.Satisfying label := by
  constructor
  · intro hpair a b hedge
    have h := hpair a b
    simpa [SatisfyingByPairs, hedge] using h
  · intro hsat a b
    by_cases hedge : T.edge a b
    · simpa [SatisfyingByPairs, hedge] using hsat a b hedge
    · simp [hedge]

/--
Lemma `lem:treecsp`: finite locally uniform edge constraints over a
process-owned finite tree have a decidable satisfying-labeling problem.
-/
noncomputable def finite_tree_csp_decidable
    {Out₁ : Type u} {Out₂ : Type v}
    [Fintype Out₁] [Fintype Out₂]
    (T : RootedConstraintTree.{u, v, w} Out₁ Out₂)
    [DecidableEq T.Vertex]
    [DecidableRel T.edge]
    [∀ a b h left right, Decidable (T.edgeRel a b h left right)] :
    Decidable (∃ label : T.Labeling, T.Satisfying label) := by
  haveI : Fintype T.Labeling := inferInstance
  haveI : (label : T.Labeling) -> Decidable (T.SatisfyingByPairs label) := by
    intro label
    dsimp [SatisfyingByPairs]
    infer_instance
  let finitePredicate : Prop :=
    ∃ label : T.Labeling, T.SatisfyingByPairs label
  have hdec : Decidable finitePredicate := inferInstance
  exact
    decidable_of_iff finitePredicate
      (by
        constructor
        · intro h
          rcases h with ⟨label, hsat⟩
          exact ⟨label, (T.satisfyingByPairs_iff label).mp hsat⟩
        · intro h
          rcases h with ⟨label, hsat⟩
          exact ⟨label, (T.satisfyingByPairs_iff label).mpr hsat⟩)

end RootedConstraintTree

end DistributedSynthesis
