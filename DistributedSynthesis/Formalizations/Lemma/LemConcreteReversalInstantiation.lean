/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPathsummary
import DistributedSynthesis.Formalizations.Lemma.LemSubstitutionWindowProfile

/-!
# Concrete instantiation bricks for the set route

Three model-facing inputs of the candidate-set reversal closure are
discharged or provided here:

* **Lawfulness of the concrete summary** (`twoBoundaryRelationSemigroup_lawful`):
  the paper's relation-valued path summary is associative with neutral
  identity relation, so the window monoid and the label profile apply to
  it directly.
* **The product refinement carrier** (`PathSummarySemigroup.prod`): the
  old-side summary is refined by pairing with the window profile;
  projections of values and windows are proved, so window equality at the
  product determines window equality of each factor.
* **The assembled pullback bound** (`prod_windowProfile_setPullbackBound`):
  at the product of any base summary with the window profile of a
  substitution scheme, window-equal old paths have equal output-window
  images -- the concrete discharge of the set-level bound for one
  refinement round over the base new-side windows.
-/

namespace DistributedSynthesis

universe u v w x y

/-! ### Lawfulness of the concrete relation-valued summary -/

theorem twoBoundaryRelationSemigroup_lawful
    (Out₁ : Type u) (Out₂ : Type v)
    [Fintype (BoundaryLabel Out₁ Out₂)]
    [DecidableEq (BoundaryLabel Out₁ Out₂)] :
    PathSummaryLawful (twoBoundaryRelationSemigroup Out₁ Out₂) where
  assoc a b c := by
    funext endpoints
    show twoBoundaryComp (twoBoundaryComp a b) c endpoints =
      twoBoundaryComp a (twoBoundaryComp b c) endpoints
    rcases endpoints with ⟨left, right⟩
    simp only [twoBoundaryComp, decide_eq_decide]
    constructor
    · rintro ⟨mid₂, hab, hc⟩
      rcases (by simpa [twoBoundaryComp] using hab :
        ∃ mid₁, a (left, mid₁) = true ∧ b (mid₁, mid₂) = true) with
        ⟨mid₁, ha, hb⟩
      exact ⟨mid₁, ha, by simp [twoBoundaryComp]; exact ⟨mid₂, hb, hc⟩⟩
    · rintro ⟨mid₁, ha, hbc⟩
      rcases (by simpa [twoBoundaryComp] using hbc :
        ∃ mid₂, b (mid₁, mid₂) = true ∧ c (mid₂, right) = true) with
        ⟨mid₂, hb, hc⟩
      exact ⟨mid₂, by simp [twoBoundaryComp]; exact ⟨mid₁, ha, hb⟩, hc⟩
  one_mul a := by
    funext endpoints
    rcases endpoints with ⟨left, right⟩
    show twoBoundaryComp twoBoundaryId a (left, right) = a (left, right)
    simp only [twoBoundaryComp, twoBoundaryId]
    by_cases h : a (left, right) = true
    · simp only [h]
      exact decide_eq_true ⟨left, by simp, h⟩
    · rw [Bool.eq_false_iff.mpr h, decide_eq_false]
      rintro ⟨mid, hmid, hma⟩
      exact h (by simpa [of_decide_eq_true hmid] using hma)
  mul_one a := by
    funext endpoints
    rcases endpoints with ⟨left, right⟩
    show twoBoundaryComp a twoBoundaryId (left, right) = a (left, right)
    simp only [twoBoundaryComp, twoBoundaryId]
    by_cases h : a (left, right) = true
    · simp only [h]
      exact decide_eq_true ⟨right, h, by simp⟩
    · rw [Bool.eq_false_iff.mpr h, decide_eq_false]
      rintro ⟨mid, hma, hmid⟩
      exact h (by simpa [<- of_decide_eq_true hmid] using hma)

/-! ### The product refinement carrier -/

namespace PathSummarySemigroup

variable {EdgeType : Type u}

/-- The product of two path-summary semigroups over one edge type. -/
def prod (S : PathSummarySemigroup.{u, v} EdgeType)
    (T : PathSummarySemigroup.{u, w} EdgeType) :
    PathSummarySemigroup.{u, max v w} EdgeType where
  Summary := S.Summary × T.Summary
  summaryFinite := by infer_instance
  empty := (S.empty, T.empty)
  ofEdge edge := (S.ofEdge edge, T.ofEdge edge)
  multiply a b := (S.multiply a.1 b.1, T.multiply a.2 b.2)

/-- Path summaries of a product are the pair of factor summaries. -/
theorem pathSummaryValue_prod (S : PathSummarySemigroup.{u, v} EdgeType)
    (T : PathSummarySemigroup.{u, w} EdgeType) (path : TypedPath EdgeType) :
    pathSummaryValue (S.prod T) path =
      (pathSummaryValue S path, pathSummaryValue T path) := by
  induction path using List.reverseRecOn with
  | nil => rfl
  | append_singleton path edge ih =>
      simp only [pathSummaryValue, List.foldl_append, List.foldl_cons,
        List.foldl_nil] at ih ⊢
      rw [ih]
      rfl

/-- Window equality at the product determines window equality at each
factor. -/
theorem summaryWindowAbstraction_prod_eq
    (S : PathSummarySemigroup.{u, v} EdgeType)
    (T : PathSummarySemigroup.{u, w} EdgeType) (c : Nat)
    {old new : TypedPath EdgeType}
    (h : summaryWindowAbstraction (S.prod T) c old =
      summaryWindowAbstraction (S.prod T) c new) :
    summaryWindowAbstraction S c old = summaryWindowAbstraction S c new ∧
      summaryWindowAbstraction T c old = summaryWindowAbstraction T c new := by
  have hsummary := congrArg SummaryWindowValue.summary h
  have hpref : prefixAtMost c old = prefixAtMost c new :=
    congrArg SummaryWindowValue.pref h
  have hsuff : suffixAtMost c old = suffixAtMost c new :=
    congrArg SummaryWindowValue.suff h
  simp only [summaryWindowAbstraction, pathSummaryValue_prod] at hsummary
  have h1 : pathSummaryValue S old = pathSummaryValue S new :=
    congrArg Prod.fst hsummary
  have h2 : pathSummaryValue T old = pathSummaryValue T new :=
    congrArg Prod.snd hsummary
  constructor <;>
    · simp only [summaryWindowAbstraction, SummaryWindowValue.mk.injEq]
      exact ⟨by assumption, hpref, hsuff⟩

end PathSummarySemigroup

/-! ### The assembled pullback bound at the product refinement -/

section Assembled

variable {OldEdge : Type u} {NewEdge : Type v} {Label : Type w}
variable [Fintype Label] [DecidableEq Label]
variable (scheme : FiniteSubstitutionScheme OldEdge NewEdge Label)
variable (Sbase : PathSummarySemigroup.{u, x} OldEdge)
variable (Snew : PathSummarySemigroup.{v, y} NewEdge)
variable [Fintype NewEdge] [DecidableEq NewEdge] [DecidableEq Snew.Summary]
variable (radius : Nat)

/-- The product-refined old-side summary: the base summary paired with
the window-valued label profile of the scheme. -/
noncomputable def refinedOldSemigroup : PathSummarySemigroup OldEdge :=
  Sbase.prod (windowProfileSemigroup scheme Snew radius)

/-- **The assembled set pullback bound**: at the product-refined old
summary, window-equal old paths (at any margin) have equal output-window
images at the profile radius. -/
theorem prod_windowProfile_setPullbackBound (hlaw : PathSummaryLawful Snew)
    (bound : Nat)
    {old₁ old₂ : TypedPath OldEdge}
    (hwindow :
      summaryWindowAbstraction (refinedOldSemigroup scheme Sbase Snew radius)
          bound old₁ =
        summaryWindowAbstraction (refinedOldSemigroup scheme Sbase Snew radius)
          bound old₂) :
    (summaryWindowAbstraction Snew radius) '' scheme.SuccessorWords old₁ =
      (summaryWindowAbstraction Snew radius) '' scheme.SuccessorWords old₂ := by
  have hproj :=
    (PathSummarySemigroup.summaryWindowAbstraction_prod_eq Sbase
      (windowProfileSemigroup scheme Snew radius) bound hwindow).2
  exact substitution_setPullbackBound scheme Snew radius hlaw bound hproj

end Assembled

end DistributedSynthesis
