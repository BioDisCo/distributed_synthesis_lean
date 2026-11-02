/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Lemma.LemEndpointwindowpreimage

/-!
# Finite closure of summary-window reversal tests
-/

namespace DistributedSynthesis

universe u v

/--
A path test is determined by the summary-window abstraction at radius `c`
when it is constant on `Σ_c`-classes.
-/
def SummaryWindowDetermines
    {EdgeType : Type u}
    (S : PathSummarySemigroup.{u, v} EdgeType)
    (c : Nat)
    (test : Set (TypedPath EdgeType)) :
    Prop :=
  ∀ old new,
    summaryWindowAbstraction S c old = summaryWindowAbstraction S c new ->
      (old ∈ test ↔ new ∈ test)

/-- Prefix windows at a larger radius determine prefix windows at a smaller radius. -/
theorem prefixAtMost_refines
    {EdgeType : Type u}
    {small large : Nat}
    (h : small ≤ large)
    (path : List EdgeType) :
    prefixAtMost small path = prefixAtMost small (prefixAtMost large path) := by
  simp [prefixAtMost, List.take_take, Nat.min_eq_left h]

/-- Reversal form of a suffix window. -/
theorem suffixAtMost_reverse
    {EdgeType : Type u}
    (c : Nat)
    (path : List EdgeType) :
    (suffixAtMost c path).reverse = prefixAtMost c path.reverse := by
  rw [suffix_eq_reverse_prefix_reverse, List.reverse_reverse]

/-- Suffix windows at a larger radius determine suffix windows at a smaller radius. -/
theorem suffixAtMost_refines
    {EdgeType : Type u}
    {small large : Nat}
    (h : small ≤ large)
    (path : List EdgeType) :
    suffixAtMost small path = suffixAtMost small (suffixAtMost large path) := by
  rw [suffix_eq_reverse_prefix_reverse, suffix_eq_reverse_prefix_reverse]
  rw [suffixAtMost_reverse]
  rw [prefixAtMost_refines h]

/-- Larger summary windows refine smaller summary windows. -/
theorem summaryWindowAbstraction_refines_of_le
    {EdgeType : Type u}
    (S : PathSummarySemigroup.{u, v} EdgeType)
    {small large : Nat}
    (h : small ≤ large)
    {old new : TypedPath EdgeType}
    (heq :
      summaryWindowAbstraction S large old =
        summaryWindowAbstraction S large new) :
    summaryWindowAbstraction S small old =
      summaryWindowAbstraction S small new := by
  have hsummary := congrArg SummaryWindowValue.summary heq
  have hpref := congrArg SummaryWindowValue.pref heq
  have hsuff := congrArg SummaryWindowValue.suff heq
  simp [summaryWindowAbstraction] at hsummary hpref hsuff ⊢
  constructor
  · exact hsummary
  · constructor
    · calc
        prefixAtMost small old =
            prefixAtMost small (prefixAtMost large old) :=
          prefixAtMost_refines h old
        _ = prefixAtMost small (prefixAtMost large new) := by
          rw [hpref]
        _ = prefixAtMost small new :=
          (prefixAtMost_refines h new).symm
    · calc
        suffixAtMost small old =
            suffixAtMost small (suffixAtMost large old) :=
          suffixAtMost_refines h old
        _ = suffixAtMost small (suffixAtMost large new) := by
          rw [hsuff]
        _ = suffixAtMost small new :=
          (suffixAtMost_refines h new).symm

/-- If a test is determined by a smaller radius, then it is determined by any larger radius. -/
theorem SummaryWindowDetermines.mono
    {EdgeType : Type u}
    (S : PathSummarySemigroup.{u, v} EdgeType)
    {small large : Nat}
    (h : small ≤ large)
    {test : Set (TypedPath EdgeType)}
    (htest : SummaryWindowDetermines S small test) :
    SummaryWindowDetermines S large test := by
  intro old new heq
  exact htest old new (summaryWindowAbstraction_refines_of_le S h heq)

/-- A one-step reversal-preimage operator respects the summary-window pullback bound. -/
def OneStepSummaryWindowPreimageBound
    {EdgeType : Type u}
    (S : PathSummarySemigroup.{u, v} EdgeType)
    (preimage : Set (TypedPath EdgeType) -> Set (TypedPath EdgeType)) :
    Prop :=
  ∀ k test,
    SummaryWindowDetermines S k test ->
      SummaryWindowDetermines S (endpointPullbackBound k) (preimage test)

/--
Corollary `cor:summarywindowfiniteclosure`, semantic core:
if each one-step reversal preimage of a `Σ_k`-test is determined by
`Σ_β(k)`, then every iterated preimage of a `Σ_c`-test is determined by the
fixed finite window radius `max c 2`.
-/
theorem summary_window_finite_closure
    {EdgeType : Type u}
    [Fintype EdgeType]
    (S : PathSummarySemigroup.{u, v} EdgeType)
    (preimage : Set (TypedPath EdgeType) -> Set (TypedPath EdgeType))
    (hone : OneStepSummaryWindowPreimageBound S preimage)
    (c n : Nat)
    (test : Set (TypedPath EdgeType))
    (htest : SummaryWindowDetermines S c test) :
    Nonempty (Fintype (FiniteSummaryWindowValue S.Summary EdgeType (max c 2))) ∧
      SummaryWindowDetermines S (max c 2) ((preimage^[n]) test) := by
  constructor
  · exact finite_summary_window_values_finite EdgeType S.Summary (max c 2)
  · have hiter :
      SummaryWindowDetermines S ((endpointPullbackBound^[n]) c) ((preimage^[n]) test) := by
      induction n with
      | zero =>
          simpa using htest
      | succ n ih =>
          rw [Function.iterate_succ_apply']
          simpa [Function.iterate_succ_apply'] using
            hone ((endpointPullbackBound^[n]) c) ((preimage^[n]) test) ih
    exact
      SummaryWindowDetermines.mono S
        (bounded_endpoint_pullback_radius c n)
        hiter

end DistributedSynthesis
