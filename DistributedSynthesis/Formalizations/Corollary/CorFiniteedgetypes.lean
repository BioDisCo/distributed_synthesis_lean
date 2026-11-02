/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Lemma.LemPathsummary

/-!
# One-step finite edge-type abstraction
-/

namespace DistributedSynthesis

universe u v w

/--
A path-level update is determined by a finite semigroup summary if equal
summary values force equal updates.
-/
def ProfileUpdateDeterminedBySemigroup
    {EdgeType : Type u} {Profile : Type v}
    (S : PathSummarySemigroup.{u, w} EdgeType)
    (update : TypedPath EdgeType -> Profile) :
    Prop :=
  ∀ old new,
    pathSummaryValue S old = pathSummaryValue S new ->
      update old = update new

/--
Corollary `cor:finiteedgetypes`: once edge types feed a finite path-summary
semigroup and the one-step profile update reads only that summary, the update
is determined by a finite semigroup product.
-/
theorem one_step_finite_edge_type_abstraction
    {EdgeType : Type u} {Profile : Type v}
    [Fintype EdgeType]
    (S : PathSummarySemigroup.{u, w} EdgeType)
    (update : TypedPath EdgeType -> Profile)
    (hupdate : ProfileUpdateDeterminedBySemigroup S update) :
    Nonempty (Fintype S.Summary) ∧
      ProfileUpdateDeterminedBySemigroup S update := by
  exact ⟨⟨S.summaryFinite⟩, hupdate⟩

end DistributedSynthesis
