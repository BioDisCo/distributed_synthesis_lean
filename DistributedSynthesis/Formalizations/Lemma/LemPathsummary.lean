/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Definition.DefPathSummary
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum

/-!
# Finite compositional path summaries
-/

namespace DistributedSynthesis

universe u v

/-- Boolean two-boundary relations over process-owned endpoint labels. -/
abbrev TwoBoundaryRelation (Out₁ : Type u) (Out₂ : Type v) :=
  BoundaryLabel Out₁ Out₂ × BoundaryLabel Out₁ Out₂ -> Bool

/-- Identity two-boundary relation. -/
def twoBoundaryId
    {Out₁ : Type u} {Out₂ : Type v}
    [DecidableEq (BoundaryLabel Out₁ Out₂)] :
    TwoBoundaryRelation Out₁ Out₂ :=
  fun endpoints => decide (endpoints.1 = endpoints.2)

/-- Relational product of two finite Boolean two-boundary relations. -/
def twoBoundaryComp
    {Out₁ : Type u} {Out₂ : Type v}
    [Fintype (BoundaryLabel Out₁ Out₂)]
    (first second : TwoBoundaryRelation Out₁ Out₂) :
    TwoBoundaryRelation Out₁ Out₂ :=
  fun endpoints =>
    decide
      (∃ mid,
        first (endpoints.1, mid) = true ∧
          second (mid, endpoints.2) = true)

/-- Membership characterization for relational product. -/
theorem twoBoundaryComp_true_iff
    {Out₁ : Type u} {Out₂ : Type v}
    [Fintype (BoundaryLabel Out₁ Out₂)]
    (first second : TwoBoundaryRelation Out₁ Out₂)
    (left right : BoundaryLabel Out₁ Out₂) :
    twoBoundaryComp first second (left, right) = true ↔
      ∃ mid, first (left, mid) = true ∧ second (mid, right) = true := by
  simp [twoBoundaryComp]

/-- Two-boundary relations over finite output alphabets form a finite type. -/
theorem two_boundary_relations_finite
    (Out₁ : Type u) (Out₂ : Type v)
    [Fintype (BoundaryLabel Out₁ Out₂)] [DecidableEq (BoundaryLabel Out₁ Out₂)] :
    Nonempty (Fintype (TwoBoundaryRelation Out₁ Out₂)) := by
  exact ⟨inferInstance⟩

/-- The canonical finite path-summary algebra whose summaries are endpoint relations. -/
def twoBoundaryRelationSemigroup
    (Out₁ : Type u) (Out₂ : Type v)
    [Fintype (BoundaryLabel Out₁ Out₂)] [DecidableEq (BoundaryLabel Out₁ Out₂)] :
    PathSummarySemigroup (TwoBoundaryRelation Out₁ Out₂) where
  Summary := TwoBoundaryRelation Out₁ Out₂
  summaryFinite := by infer_instance
  empty := twoBoundaryId
  ofEdge := id
  multiply := twoBoundaryComp

/-- Summary of a typed path of edge relations. -/
def relationPathSummary
    {Out₁ : Type u} {Out₂ : Type v}
    [Fintype (BoundaryLabel Out₁ Out₂)] [DecidableEq (BoundaryLabel Out₁ Out₂)]
    (path : TypedPath (TwoBoundaryRelation Out₁ Out₂)) :
    TwoBoundaryRelation Out₁ Out₂ :=
  pathSummaryValue (twoBoundaryRelationSemigroup Out₁ Out₂) path

@[simp]
theorem relationPathSummary_nil
    {Out₁ : Type u} {Out₂ : Type v}
    [Fintype (BoundaryLabel Out₁ Out₂)] [DecidableEq (BoundaryLabel Out₁ Out₂)] :
    relationPathSummary ([] : TypedPath (TwoBoundaryRelation Out₁ Out₂)) =
      twoBoundaryId := by
  rfl

/-- Appending one edge multiplies the previous path summary by that edge relation. -/
theorem relationPathSummary_snoc
    {Out₁ : Type u} {Out₂ : Type v}
    [Fintype (BoundaryLabel Out₁ Out₂)] [DecidableEq (BoundaryLabel Out₁ Out₂)]
    (path : TypedPath (TwoBoundaryRelation Out₁ Out₂))
    (edge : TwoBoundaryRelation Out₁ Out₂) :
    relationPathSummary (path ++ [edge]) =
      twoBoundaryComp (relationPathSummary path) edge := by
  simp [relationPathSummary, pathSummaryValue, twoBoundaryRelationSemigroup]

/--
Lemma `lem:pathsummary`: finite two-boundary summaries are endpoint-label
relations, and their composition is relational product.
-/
theorem finite_compositional_path_summaries
    (Out₁ : Type u) (Out₂ : Type v)
    [Fintype (BoundaryLabel Out₁ Out₂)] [DecidableEq (BoundaryLabel Out₁ Out₂)] :
    Nonempty (Fintype (TwoBoundaryRelation Out₁ Out₂)) ∧
      ∀ first second left right,
        twoBoundaryComp (Out₁ := Out₁) (Out₂ := Out₂) first second (left, right) = true ↔
          ∃ mid, first (left, mid) = true ∧ second (mid, right) = true := by
  constructor
  · exact two_boundary_relations_finite Out₁ Out₂
  · intro first second left right
    exact twoBoundaryComp_true_iff first second left right

/--
Lemma `lem:pathsemigroup`: for finite output alphabets, labelled paths have a
finite relation-valued summary algebra, and the path summary is the fold product
of edge summaries.
-/
theorem finite_semigroup_summary_of_typed_paths
    (Out₁ : Type u) (Out₂ : Type v)
    [Fintype (BoundaryLabel Out₁ Out₂)] [DecidableEq (BoundaryLabel Out₁ Out₂)]
    (path : TypedPath (TwoBoundaryRelation Out₁ Out₂)) :
    Nonempty (Fintype (TwoBoundaryRelation Out₁ Out₂)) ∧
      relationPathSummary path =
        path.foldl
          (fun acc edge => twoBoundaryComp acc edge)
          (twoBoundaryId (Out₁ := Out₁) (Out₂ := Out₂)) := by
  constructor
  · exact two_boundary_relations_finite Out₁ Out₂
  · rfl

end DistributedSynthesis
