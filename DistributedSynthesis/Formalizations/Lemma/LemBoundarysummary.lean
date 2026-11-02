/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemTreecsp

/-!
# Boundary summaries

This file formalizes the finite and decidable core of `lem:boundarysummary`
for the rooted constraint-tree model used by `def:boundarysummary`.
-/

namespace DistributedSynthesis

universe u v w

namespace RootedConstraintTree

/-- Boundary summaries range over labels of the finite root alphabet. -/
theorem boundary_summary_root_labels_finite
    {Out₁ : Type u} {Out₂ : Type v}
    [Fintype Out₁] [Fintype Out₂]
    (T : RootedConstraintTree.{u, v, w} Out₁ Out₂) :
    Nonempty (Fintype (OwnedLabel Out₁ Out₂ (T.owner T.root))) := by
  exact ⟨inferInstance⟩

/-- Membership in the semantic boundary summary is a finite decidable search. -/
noncomputable def boundary_summary_membership_decidable
    {Out₁ : Type u} {Out₂ : Type v}
    [Fintype Out₁] [Fintype Out₂]
    (T : RootedConstraintTree.{u, v, w} Out₁ Out₂)
    [DecidableEq T.Vertex]
    [DecidableRel T.edge]
    [∀ a b h left right, Decidable (T.edgeRel a b h left right)]
    [DecidableEq (OwnedLabel Out₁ Out₂ (T.owner T.root))]
    (rootLabel : OwnedLabel Out₁ Out₂ (T.owner T.root)) :
    Decidable (rootLabel ∈ boundarySummary T) := by
  haveI : Fintype T.Labeling := inferInstance
  haveI : (label : T.Labeling) -> Decidable (T.SatisfyingByPairs label) := by
    intro label
    dsimp [SatisfyingByPairs]
    infer_instance
  let finitePredicate : Prop :=
    ∃ label : T.Labeling,
      T.SatisfyingByPairs label ∧ label T.root = rootLabel
  have hdec : Decidable finitePredicate := inferInstance
  exact
    decidable_of_iff finitePredicate
      (by
        constructor
        · intro h
          rcases h with ⟨label, hsat, hroot⟩
          exact ⟨label, (T.satisfyingByPairs_iff label).mp hsat, hroot⟩
        · intro h
          rcases h with ⟨label, hsat, hroot⟩
          exact ⟨label, (T.satisfyingByPairs_iff label).mpr hsat, hroot⟩)

/--
Lemma `lem:boundarysummary`: boundary-summary membership is exactly the finite
search over satisfying labelings whose root label is the queried boundary
label.
-/
theorem boundary_summary_membership_iff_finite_search
    {Out₁ : Type u} {Out₂ : Type v}
    (T : RootedConstraintTree.{u, v, w} Out₁ Out₂)
    [DecidableRel T.edge]
    (rootLabel : OwnedLabel Out₁ Out₂ (T.owner T.root)) :
    rootLabel ∈ boundarySummary T ↔
      ∃ label : T.Labeling,
        T.SatisfyingByPairs label ∧ label T.root = rootLabel := by
  constructor
  · intro h
    rcases h with ⟨label, hsat, hroot⟩
    exact ⟨label, (T.satisfyingByPairs_iff label).mpr hsat, hroot⟩
  · intro h
    rcases h with ⟨label, hsat, hroot⟩
    exact ⟨label, (T.satisfyingByPairs_iff label).mp hsat, hroot⟩

end RootedConstraintTree

end DistributedSynthesis
