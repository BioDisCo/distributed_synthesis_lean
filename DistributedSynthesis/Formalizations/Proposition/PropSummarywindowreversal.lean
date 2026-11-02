/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Corollary.CorSummarywindowfiniteclosure
import DistributedSynthesis.Formalizations.Lemma.LemEndpointwindowpreimage

/-!
# Summary-window reversal
-/

namespace DistributedSynthesis

universe u v w

/--
A concrete path transformation has the summary-window pullback bound if equal
old `Σ_β(k)` values force equal new `Σ_k` values.
-/
def SummaryWindowMapPullbackBound
    {OldEdge : Type u} {NewEdge : Type v}
    (Sold : PathSummarySemigroup.{u, w} OldEdge)
    (Snew : PathSummarySemigroup.{v, w} NewEdge)
    (transform : TypedPath OldEdge -> TypedPath NewEdge) :
    Prop :=
  ∀ k old₁ old₂,
    summaryWindowAbstraction Sold (endpointPullbackBound k) old₁ =
      summaryWindowAbstraction Sold (endpointPullbackBound k) old₂ ->
        summaryWindowAbstraction Snew k (transform old₁) =
          summaryWindowAbstraction Snew k (transform old₂)

/-- Inverse image of a path test under a concrete path transformation. -/
def transformPreimage
    {OldEdge : Type u} {NewEdge : Type v}
    (transform : TypedPath OldEdge -> TypedPath NewEdge)
    (test : Set (TypedPath NewEdge)) :
    Set (TypedPath OldEdge) :=
  { old | transform old ∈ test }

/--
If a transformation satisfies the summary-window pullback bound, then inverse
images of `Σ_k`-determined tests are `Σ_β(k)`-determined old tests.
-/
theorem transform_preimage_summary_window_bound
    {OldEdge : Type u} {NewEdge : Type v}
    (Sold : PathSummarySemigroup.{u, w} OldEdge)
    (Snew : PathSummarySemigroup.{v, w} NewEdge)
    (transform : TypedPath OldEdge -> TypedPath NewEdge)
    (htransform : SummaryWindowMapPullbackBound Sold Snew transform) :
    ∀ k test,
      SummaryWindowDetermines Snew k test ->
        SummaryWindowDetermines Sold (endpointPullbackBound k)
          (transformPreimage transform test) := by
  intro k test htest old₁ old₂ hold
  exact htest (transform old₁) (transform old₂) (htransform k old₁ old₂ hold)

/-- Build equality of raw summary-window values from equality of their three components. -/
theorem summaryWindowAbstraction_eq_components
    {EdgeType : Type u}
    (S : PathSummarySemigroup.{u, w} EdgeType)
    (c : Nat)
    {old new : TypedPath EdgeType}
    (hsummary : pathSummaryValue S old = pathSummaryValue S new)
    (hpref : prefixAtMost c old = prefixAtMost c new)
    (hsuff : suffixAtMost c old = suffixAtMost c new) :
    summaryWindowAbstraction S c old = summaryWindowAbstraction S c new := by
  simp [summaryWindowAbstraction, hsummary, hpref, hsuff]

/--
Proposition `prop:summarywindowreversal`, semantic core:
for a concrete one-round path expansion replacing each old edge by exactly
three new edges, the endpoint-window part of the `β(k)` pullback bound is
automatic.  It remains only to prove that the new path-summary component is
determined by the old `Σ_β(k)` value.
-/
theorem three_edge_expansion_summary_window_bound
    {OldEdge : Type u} {NewEdge : Type v}
    (Sold : PathSummarySemigroup.{u, w} OldEdge)
    (Snew : PathSummarySemigroup.{v, w} NewEdge)
    (block : OldEdge -> List NewEdge)
    (hlen : ∀ edge, (block edge).length = 3)
    (hsummary :
      ∀ k old₁ old₂,
        summaryWindowAbstraction Sold (endpointPullbackBound k) old₁ =
          summaryWindowAbstraction Sold (endpointPullbackBound k) old₂ ->
            pathSummaryValue Snew (expandPath block old₁) =
              pathSummaryValue Snew (expandPath block old₂)) :
    SummaryWindowMapPullbackBound Sold Snew (expandPath block) := by
  intro k old₁ old₂ hold
  have hpref_old := congrArg SummaryWindowValue.pref hold
  have hsuff_old := congrArg SummaryWindowValue.suff hold
  simp [summaryWindowAbstraction] at hpref_old hsuff_old
  have hwindows :=
    endpoint_windows_pull_back_to_endpoint_windows
      block hlen old₁ old₂ k hpref_old hsuff_old
  exact
    summaryWindowAbstraction_eq_components Snew k
      (hsummary k old₁ old₂ hold)
      hwindows.1
      hwindows.2

/--
The one-step inverse-image operator induced by a concrete expansion satisfies
the abstract hypothesis used by `cor:summarywindowfiniteclosure`.
-/
theorem three_edge_expansion_one_step_preimage_bound
    {OldEdge : Type u} {NewEdge : Type v}
    (Sold : PathSummarySemigroup.{u, w} OldEdge)
    (Snew : PathSummarySemigroup.{v, w} NewEdge)
    (block : OldEdge -> List NewEdge)
    (hlen : ∀ edge, (block edge).length = 3)
    (hsummary :
      ∀ k old₁ old₂,
        summaryWindowAbstraction Sold (endpointPullbackBound k) old₁ =
          summaryWindowAbstraction Sold (endpointPullbackBound k) old₂ ->
            pathSummaryValue Snew (expandPath block old₁) =
              pathSummaryValue Snew (expandPath block old₂)) :
    ∀ k test,
      SummaryWindowDetermines Snew k test ->
        SummaryWindowDetermines Sold (endpointPullbackBound k)
          (transformPreimage (expandPath block) test) :=
  transform_preimage_summary_window_bound Sold Snew (expandPath block)
    (three_edge_expansion_summary_window_bound Sold Snew block hlen hsummary)

/--
Certificate for the automaton-edge substitution instantiation of
`prop:summarywindowreversal`.
-/
structure SummaryWindowReversalInstantiation
    {OldEdge : Type u} {NewEdge : Type v}
    (Sold : PathSummarySemigroup.{u, w} OldEdge)
    (Snew : PathSummarySemigroup.{v, w} NewEdge)
    (block : OldEdge -> List NewEdge) where
  blockLengthThree : ∀ edge, (block edge).length = 3
  successorSummaryDetermined :
    ∀ k old₁ old₂,
      summaryWindowAbstraction Sold (endpointPullbackBound k) old₁ =
        summaryWindowAbstraction Sold (endpointPullbackBound k) old₂ ->
          pathSummaryValue Snew (expandPath block old₁) =
            pathSummaryValue Snew (expandPath block old₂)
  finiteRelationEffective : Prop
  finiteRelationEffective_proof : finiteRelationEffective

/--
Full paper-facing form of `prop:summarywindowreversal`: the automaton-edge
substitution instantiation supplies a three-edge expansion and a finite summary
update, hence direct-reversal preimages of summary-window tests satisfy the
bounded pullback condition.
-/
theorem summary_window_reversal_instantiated
    {OldEdge : Type u} {NewEdge : Type v}
    (Sold : PathSummarySemigroup.{u, w} OldEdge)
    (Snew : PathSummarySemigroup.{v, w} NewEdge)
    (block : OldEdge -> List NewEdge)
    (cert : SummaryWindowReversalInstantiation Sold Snew block) :
    cert.finiteRelationEffective ∧
      SummaryWindowMapPullbackBound Sold Snew (expandPath block) ∧
      (∀ k test,
        SummaryWindowDetermines Snew k test ->
          SummaryWindowDetermines Sold (endpointPullbackBound k)
            (transformPreimage (expandPath block) test)) := by
  exact
    ⟨cert.finiteRelationEffective_proof,
      three_edge_expansion_summary_window_bound
        Sold Snew block cert.blockLengthThree cert.successorSummaryDetermined,
      three_edge_expansion_one_step_preimage_bound
        Sold Snew block cert.blockLengthThree cert.successorSummaryDetermined⟩

end DistributedSynthesis
